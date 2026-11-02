/-
Zakura's own ZIP 243 signature digest, which its node signs and verifies version 4 transactions
with: `zakura-chain` 10.0.0, `src/transaction/sighash/v4.rs`, over its parsed version 4
transaction (`src/transaction.rs`, `src/sprout/joinsplit.rs`, `src/transaction/joinsplit.rs`,
`src/sapling/`).

The `SIGHASH_*` constants are `zakura-transparent` 4.0.0's (`src/sighash.rs`, lines 11–15), the
same as `zcash_transparent` 0.11.0's at the same lines (`Verifier/Transparent.lean`).
-/
module

public import ZcashSighash.Verifier.Native

@[expose] public section

namespace ZcashSighash.Verifier.Native.V4

open Spec (Byte Bytes personal)
open Orchard (update finalize)
open Transparent (SIGHASH_ALL SIGHASH_NONE SIGHASH_SINGLE SIGHASH_MASK SIGHASH_ANYONECANPAY)

/-! ## The version 4 transaction -/

/-- A Sprout `JoinSplit<Groth16Proof>` (`src/sprout/joinsplit.rs`, lines 64–92), its fields as
    their encodings. -/
structure JoinSplit where
  vpubOld : BitVec 64
  vpubNew : BitVec 64
  anchor : Bytes 32
  nullifiers : Bytes 32 × Bytes 32
  commitments : Bytes 32 × Bytes 32
  ephemeralKey : Bytes 32
  randomSeed : Bytes 32
  vmacs : Bytes 32 × Bytes 32
  zkproof : Bytes 192
  encCiphertexts : Bytes 601 × Bytes 601

/-- `JoinSplit::zcash_serialize` (`src/sprout/joinsplit.rs`, lines 143–168). An
    `Amount<NonNegative>` writes its value as a `u64` (`src/amount.rs`, lines 694–707). -/
def JoinSplit.serialize (js : JoinSplit) : List Byte :=
  toLeBytes 8 js.vpubOld ++ toLeBytes 8 js.vpubNew ++ js.anchor.toList ++
    js.nullifiers.1.toList ++ js.nullifiers.2.toList ++ js.commitments.1.toList ++
    js.commitments.2.toList ++ js.ephemeralKey.toList ++ js.randomSeed.toList ++
    js.vmacs.1.toList ++ js.vmacs.2.toList ++ js.zkproof.toList ++ js.encCiphertexts.1.toList ++
    js.encCiphertexts.2.toList

/-- `JoinSplitData<Groth16Proof>` (`src/transaction/joinsplit.rs`, lines 22–51): at least one
    JoinSplit, by its type. -/
structure JoinSplitData where
  first : JoinSplit
  rest : List JoinSplit
  pubKey : Bytes 32
  sig : Bytes 64

/-- `JoinSplitData::joinsplits` (`src/transaction/joinsplit.rs`, lines 85–87). -/
def JoinSplitData.joinsplits (self : JoinSplitData) : List JoinSplit := self.first :: self.rest

/-- A Sapling `Spend<PerSpendAnchor>` (`src/sapling/spend.rs`, lines 38–65), its fields as
    their encodings. -/
structure Spend where
  cv : Bytes 32
  perSpendAnchor : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  zkproof : Bytes 192
  spendAuthSig : Bytes 64

/-- `TransferData<PerSpendAnchor>` (`src/sapling/shielded_data.rs`, lines 124–173), whose shared
    anchor is absent: Spends and maybe Outputs, or just Outputs. -/
inductive Transfers where
  | spendsAndMaybeOutputs (spends : Orchard.NonEmpty Spend) (maybeOutputs : List SaplingOutput)
  | justOutputs (outputs : Orchard.NonEmpty SaplingOutput)

/-- `ShieldedData<PerSpendAnchor>` (`src/sapling/shielded_data.rs`, lines 90–111). -/
structure SaplingData where
  valueBalance : BitVec 64
  transfers : Transfers
  bindingSig : Bytes 64

/-- `ShieldedData::spends` (lines 258–260), through `TransferData::spends` (lines 388–399). -/
def SaplingData.spends (s : SaplingData) : List Spend :=
  match s.transfers with
  | .spendsAndMaybeOutputs spends _ => spends.toList
  | .justOutputs _ => []

/-- `ShieldedData::outputs` (lines 264–266), through `TransferData::outputs` (lines 402–410). -/
def SaplingData.outputs (s : SaplingData) : List SaplingOutput :=
  match s.transfers with
  | .spendsAndMaybeOutputs _ maybeOutputs => maybeOutputs
  | .justOutputs outputs => outputs.toList

/-- `OutputInTransactionV4::zcash_serialize` (`src/sapling/output.rs`, lines 131–142). -/
def _root_.ZcashSighash.Verifier.Native.SaplingOutput.serializeV4 (o : SaplingOutput) :
    List Byte :=
  o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList ++
    o.outCiphertext.toList ++ o.zkproof.toList

/-- `Transaction::V4` (`src/transaction.rs`, lines 114–128), with `raw_lock_time`
    (lines 648–666): the lock time's four bytes, as a `u32`. -/
structure Transaction where
  inputs : List Input
  outputs : List Output
  lockTime : BitVec 32
  expiryHeight : BitVec 32
  joinsplitData : Option JoinSplitData
  saplingShieldedData : Option SaplingData

/-- `Input::outpoint` (`src/transparent.rs`, lines 211–217). -/
def _root_.ZcashSighash.Verifier.Native.Input.outpoint : Input → Option OutPoint
  | .prevOut o _ _ => some o
  | .coinbase .. => none

/-! ## `src/transaction/sighash/v4.rs` -/

/-- `OVERWINTERED_FLAG` (line 28). -/
def OVERWINTERED_FLAG : BitVec 32 := 1 <<< 31

/-- `V4_VERSION` (line 29). -/
def V4_VERSION : BitVec 32 := 4

/-- `SAPLING_VERSION_GROUP_ID` (`src/parameters/transaction.rs`, line 7). -/
def SAPLING_VERSION_GROUP_ID : BitVec 32 := 0x892F2085

/-- `ZERO_DIGEST` (line 31). -/
def ZERO_DIGEST : List Byte := List.replicate 32 0

/-- `update_outpoint` (lines 59–67). `update_serialized` (lines 53–57) cannot fail on an
    outpoint. -/
def updateOutpoint (state : Blake2b.State) (input : Input) : Blake2b.State :=
  match input with
  | .prevOut outpoint .. => update state outpoint.serialize
  | .coinbase .. =>
    let state := update state (List.replicate 32 0)
    update state (toLeBytes 4 (0xffffffff : BitVec 32))

/-- `prevouts_hash` (lines 69–75). -/
def prevoutsHash (inputs : List Input) : Option Blake2bHash := do
  let mut state ← hasher (personal "ZcashPrevoutHash")
  for input in inputs do
    state := updateOutpoint state input
  pure (finalize state)

/-- `sequence_hash` (lines 77–83). -/
def sequenceHash (inputs : List Input) : Option Blake2bHash := do
  let mut state ← hasher (personal "ZcashSequencHash")
  for input in inputs do
    state := update state (toLeBytes 4 input.sequence)
  pure (finalize state)

/-- `output_hash` (lines 85–89): `update_serialized` panics if serializing fails. -/
def outputHash (output : Output) : Option Blake2bHash := do
  let mut state ← hasher (personal "ZcashOutputsHash")
  state ← updateSerialized state output.serialize
  pure (finalize state)

/-- `outputs_hash` (lines 91–97). -/
def outputsHash (outputs : List Output) : Option Blake2bHash := do
  let mut state ← hasher (personal "ZcashOutputsHash")
  for output in outputs do
    state ← updateSerialized state output.serialize
  pure (finalize state)

/-- `joinsplits_hash` (lines 99–109); a JoinSplit's serialization cannot fail. The outer
    `Option` is a panic. -/
def joinsplitsHash (joinsplitData : Option JoinSplitData) : Option (Option Blake2bHash) := do
  let some joinsplitData := joinsplitData | pure none
  let mut state ← hasher (personal "ZcashJSplitsHash")
  for joinsplit in joinsplitData.joinsplits do
    state := update state joinsplit.serialize
  state := update state joinsplitData.pubKey.toList
  pure (some (finalize state))

/-- `sapling_spends_hash` (lines 111–125); an anchor's and a proof's serialization cannot
    fail. -/
def saplingSpendsHash (shieldedData : SaplingData) : Option (Option Blake2bHash) := do
  if shieldedData.spends.isEmpty then return none
  let mut state ← hasher (personal "ZcashSSpendsHash")
  for spend in shieldedData.spends do
    state := update state spend.cv.toList
    state := update state spend.perSpendAnchor.toList
    state := update state spend.nullifier.toList
    state := update state spend.rk.toList
    state := update state spend.zkproof.toList
  pure (some (finalize state))

/-- `sapling_outputs_hash` (lines 127–137); an output's serialization cannot fail. -/
def saplingOutputsHash (shieldedData : SaplingData) : Option (Option Blake2bHash) := do
  if shieldedData.outputs.isEmpty then return none
  let mut state ← hasher (personal "ZcashSOutputHash")
  for output in shieldedData.outputs do
    state := update state output.serializeV4
  pure (some (finalize state))

/-- `InputTail` (lines 139–143). -/
structure InputTail where
  outpoint : Option OutPoint
  sequence : BitVec 32

/-- `V4Sighash` (lines 145–161). -/
structure V4Sighash where
  consensusBranchId : BitVec 32
  lockTime : BitVec 32
  expiryHeight : BitVec 32
  inputs : List InputTail
  previousOutputValues : List (BitVec 64)
  prevouts : Blake2bHash
  sequence : Blake2bHash
  outputs : Blake2bHash
  singleOutputs : List Blake2bHash
  joinsplits : Option Blake2bHash
  valueBalance : BitVec 64
  saplingSpends : Option Blake2bHash
  saplingOutputs : Option Blake2bHash

/-- `V4Sighash::new` (lines 165–216), for a version 4 transaction, with the network upgrade's
    branch ID (`none` for one without). The outer `Option` is a panic. -/
def V4Sighash.new (tx : Transaction) (branchId : Option (BitVec 32))
    (allPreviousOutputs : List Output) : Option (Option V4Sighash) := do
  let some consensusBranchId := branchId | pure none
  let valueBalance := (tx.saplingShieldedData.map (·.valueBalance)).getD 0
  let saplingSpends ← match tx.saplingShieldedData with
    | some data => saplingSpendsHash data
    | none => pure none
  let saplingOutputs ← match tx.saplingShieldedData with
    | some data => saplingOutputsHash data
    | none => pure none
  pure (some
    { consensusBranchId
      lockTime := tx.lockTime
      expiryHeight := tx.expiryHeight
      inputs := tx.inputs.map fun input => ⟨input.outpoint, input.sequence⟩
      previousOutputValues := allPreviousOutputs.map (·.value)
      prevouts := ← prevoutsHash tx.inputs
      sequence := ← sequenceHash tx.inputs
      outputs := ← outputsHash tx.outputs
      singleOutputs := ← (tx.outputs.take tx.inputs.length).mapM outputHash
      joinsplits := ← joinsplitsHash tx.joinsplitData
      valueBalance
      saplingSpends
      saplingOutputs })

/-- `V4Sighash::signature_hash` (lines 222–322). The outer `Option` is a panic: serializing
    `script_code` fails if it is longer than `MAX_PROTOCOL_MESSAGE_LEN`. -/
def V4Sighash.signatureHash (self : V4Sighash) (rawHashType : Byte)
    (inputIndexScriptCode : Option (ℕ × List Byte)) : Option (Option Blake2bHash) := do
  let transparentInput ← match inputIndexScriptCode with
    | some (index, scriptCode) =>
      match self.inputs[index]?, self.previousOutputValues[index]? with
      | some input, some value => pure (some (input, value, index, scriptCode))
      | _, _ => return none
    | none => pure none
  let rawHashType := if transparentInput.isSome then rawHashType else SIGHASH_ALL
  let outputMode := rawHashType &&& SIGHASH_MASK
  let mut state ← hasher (branchPersonalization (Spec.ascii "ZcashSigHash" 12)
    self.consensusBranchId)
  state := update state (toLeBytes 4 (OVERWINTERED_FLAG ||| V4_VERSION))
  state := update state (toLeBytes 4 SAPLING_VERSION_GROUP_ID)
  if rawHashType &&& SIGHASH_ANYONECANPAY == 0 then
    state := update state self.prevouts
  else
    state := update state ZERO_DIGEST
  if rawHashType &&& SIGHASH_ANYONECANPAY == 0 && outputMode != SIGHASH_SINGLE &&
      outputMode != SIGHASH_NONE then
    state := update state self.sequence
  else
    state := update state ZERO_DIGEST
  if outputMode != SIGHASH_SINGLE && outputMode != SIGHASH_NONE then
    state := update state self.outputs
  else if outputMode == SIGHASH_SINGLE then
    match transparentInput.bind fun (_, _, index, _) => self.singleOutputs[index]? with
    | some output => state := update state output
    | none => state := update state ZERO_DIGEST
  else
    state := update state ZERO_DIGEST
  state := update state (self.joinsplits.getD ZERO_DIGEST)
  state := update state (self.saplingSpends.getD ZERO_DIGEST)
  state := update state (self.saplingOutputs.getD ZERO_DIGEST)
  state := update state (toLeBytes 4 self.lockTime)
  state := update state (toLeBytes 4 self.expiryHeight)
  state := update state (toLeBytes 8 self.valueBalance)
  state := update state (toLeBytes 4 (rawHashType.setWidth 32))
  if let some (input, value, _, scriptCode) := transparentInput then
    match input.outpoint with
    | some outpoint => state := update state outpoint.serialize
    | none =>
      state := update state (List.replicate 32 0)
      state := update state (toLeBytes 4 (0xffffffff : BitVec 32))
    state ← updateSerialized state (serializeBytes scriptCode)
    state := update state (toLeBytes 8 value)
    state := update state (toLeBytes 4 input.sequence)
  pure (some (finalize state))

/-- `SigHasher::sighash_v4_raw` (`src/transaction/sighash.rs`, lines 261–289) for a version 4
    transaction, whose `v4` data is `v4`: the `expect` panics where `signature_hash` returns
    `None`. -/
def sigHasherSighashV4Raw (v4 : V4Sighash) (rawHashType : Byte)
    (inputIndexScriptCode : Option (ℕ × List Byte)) : Option Blake2bHash :=
  (v4.signatureHash rawHashType inputIndexScriptCode).join

end ZcashSighash.Verifier.Native.V4
