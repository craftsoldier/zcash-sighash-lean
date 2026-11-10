/-
`zcash_primitives` 0.31.0's version 3 and 4 signature digests (ZIP 143, ZIP 243;
`src/transaction/sighash_v4.rs`), with the version 4 Sapling Output encoding
(`src/transaction/components/sapling.rs`) and the `TxVersion` predicates they test
(`src/transaction/mod.rs`).

`PrecomputedSighashData::new` holds `TxDigests::Zip143(zip143_digests(&tx))` for these versions
(`sighash.rs`, lines 64–66), and `signature_hash` calls `v4_signature_hash` with them (line 151).
-/
module

public import ZcashSighash.Verifier.Sighash

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)
open Transparent (SIGHASH_ANYONECANPAY SIGHASH_MASK SIGHASH_NONE SIGHASH_SINGLE)
open Orchard (update finalize)

/-- `TxVersion::has_sprout` (`mod.rs`, lines 157–166). -/
def TxVersion.hasSprout : TxVersion → Bool
  | .sprout v => v.toNat ≥ 2
  | .v3 | .v4 => true
  | .v5 | .v6 => false

/-- `TxVersion::has_overwinter` (`mod.rs`, lines 168–170). -/
def TxVersion.hasOverwinter : TxVersion → Bool
  | .sprout _ => false
  | _ => true

/-- `TxVersion::has_sapling` (`mod.rs`, lines 173–182). -/
def TxVersion.hasSapling : TxVersion → Bool
  | .sprout _ | .v3 => false
  | _ => true

/-- `TransactionData::sapling_value_balance` (`mod.rs`, lines 876–880). -/
def TransactionData.saplingValueBalance (self : TransactionData) : BitVec 64 :=
  (self.saplingBundle.map (·.valueBalance)).getD 0

/-- `write_output_v4` (`components/sapling.rs`, lines 321–331). -/
def writeOutputV4 {W : Type} [Write W] (writer : W) (output : Sapling.OutputDescription) :
    IoResult W := do
  let writer ← Write.writeAll writer output.cv.toList
  let writer ← Write.writeAll writer output.cmu.toList
  let writer ← Write.writeAll writer output.ephemeralKey.toList
  let writer ← Write.writeAll writer output.encCiphertext.toList
  let writer ← Write.writeAll writer output.outCiphertext.toList
  Write.writeAll writer output.zkproof.toList

/-- `Params::new().hash_length(32).personal(personal).hash(&data)`. With no key, `Params::hash`
    (`blake2b_simd` 1.0.4, `src/lib.rs`, lines 208–226) compresses `data` directly: BLAKE2b of
    it, as `State::finalize` gives. -/
def hashWith (personal : Bytes 16) (data : List Byte) : Option Blake2bHash := do
  let params ← Blake2b.Params.new.hashLength? 32
  let params ← params.personal? (personal.toList.map (·.toNat))
  pure ((Blake2b.blake2b params.hashLength params.personal (data.map (·.toNat))).map
    (BitVec.ofNat 8))

/-- `update_hash!` (lines 26–34): the value, or 32 zero bytes. -/
def updateHash (h : Blake2b.State) (cond : Bool) (value : Blake2bHash) : Blake2b.State :=
  if cond then update h value else update h (List.replicate 32 0)

/-- `prevout_hash` (lines 36–45). -/
def prevoutHash (vin : List Transparent.TxIn) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for tIn in vin do
    data ← unwrap (tIn.prevout.write data)
  hashWith (personal "ZcashPrevoutHash") data

/-- `sequence_hash` (lines 47–56). -/
def sequenceHash (vin : List Transparent.TxIn) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for tIn in vin do
    data := data ++ toLeBytes 4 tIn.sequence
  hashWith (personal "ZcashSequencHash") data

/-- `outputs_hash` (lines 58–67). -/
def outputsHash (vout : List Transparent.TxOut) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for tOut in vout do
    data ← unwrap (tOut.write data)
  hashWith (personal "ZcashOutputsHash") data

/-- `single_output_hash` (lines 69–76). -/
def singleOutputHash (txOut : Transparent.TxOut) : Option Blake2bHash := do
  let data ← unwrap (txOut.write ([] : VecU8))
  hashWith (personal "ZcashOutputsHash") data

/-- `joinsplits_hash` (lines 78–99). The branch ID only sizes the buffer. -/
def joinsplitsHash (joinsplits : List Sprout.JsDescription) (joinsplitPubkey : Bytes 32) :
    Option Blake2bHash := do
  let mut data : VecU8 := []
  for js in joinsplits do
    data ← unwrap (js.write data)
  data := data ++ joinsplitPubkey.toList
  hashWith (personal "ZcashJSplitsHash") data

/-- `sapling_spends_hash` (lines 101–118). -/
def saplingSpendsHash (spends : List Sapling.SpendDescription) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for sSpend in spends do
    data := data ++ sSpend.cv.toList
    data := data ++ sSpend.anchor.toList
    data := data ++ sSpend.nullifier.toList
    data := data ++ sSpend.rk.toList
    data := data ++ sSpend.zkproof.toList
  hashWith (personal "ZcashSSpendsHash") data

/-- `sapling_outputs_hash` (lines 120–129). -/
def saplingOutputsHash (outputs : List Sapling.OutputDescription) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for sOut in outputs do
    data ← unwrap (writeOutputV4 data sOut)
  hashWith (personal "ZcashSOutputHash") data

/-- `Zip143Digests` (`mod.rs`, lines 1358–1368). -/
structure Zip143Digests where
  transparent : TransparentDigests
  joinsplits : Option Blake2bHash
  saplingSpends : Option Blake2bHash
  saplingOutputs : Option Blake2bHash

/-- `zip143_digests` (lines 136–173). -/
def zip143Digests (tx : TransactionData) : Option Zip143Digests := do
  let vin := (tx.transparentBundle.map (·.vin)).getD []
  let vout := (tx.transparentBundle.map (·.vout)).getD []
  let joinsplits ← match tx.sproutBundle.filter (!·.joinsplits.isEmpty) with
    | none => pure none
    | some b => some <$> joinsplitsHash b.joinsplits b.joinsplitPubkey
  let saplingSpends ← match tx.saplingBundle.filter (!·.shieldedSpends.isEmpty) with
    | none => pure none
    | some b => some <$> saplingSpendsHash b.shieldedSpends
  let saplingOutputs ← match tx.saplingBundle.filter (!·.shieldedOutputs.isEmpty) with
    | none => pure none
    | some b => some <$> saplingOutputsHash b.shieldedOutputs
  pure ⟨⟨← prevoutHash vin, ← sequenceHash vin, ← outputsHash vout⟩, joinsplits, saplingSpends,
    saplingOutputs⟩

/-- `v4_signature_hash` (lines 184–283): a panic for a version before Overwinter, and for a
    transparent input without a transparent bundle or out of its range. -/
def v4SignatureHash (tx : TransactionData) (signableInput : SignableInput)
    (digests : Zip143Digests) : Option Blake2bHash := do
  let hashType := signableInput.hashType
  if !tx.version.hasOverwinter then none
  let params ← Blake2b.Params.new.hashLength? 32
  let params ← params.personal?
    ((branchPersonalization (Spec.ascii "ZcashSigHash" 12) tx.consensusBranchId).toList.map
      (·.toNat))
  let mut h := params.toState
  h := update h (toLeBytes 4 tx.version.header)
  h := update h (toLeBytes 4 tx.version.versionGroupId)
  h := updateHash h (hashType &&& SIGHASH_ANYONECANPAY == 0) digests.transparent.prevoutsDigest
  h := updateHash h (hashType &&& SIGHASH_ANYONECANPAY == 0 &&
      hashType &&& SIGHASH_MASK != SIGHASH_SINGLE && hashType &&& SIGHASH_MASK != SIGHASH_NONE)
    digests.transparent.sequenceDigest
  if hashType &&& SIGHASH_MASK != SIGHASH_SINGLE && hashType &&& SIGHASH_MASK != SIGHASH_NONE then
    h := update h digests.transparent.outputsDigest
  else if hashType &&& SIGHASH_MASK == SIGHASH_SINGLE then
    match tx.transparentBundle, signableInput with
    | some b, .transparent input =>
      if input.index < b.vout.length then
        h := update h (← singleOutputHash (← b.vout[input.index]?))
      else h := update h (List.replicate 32 0)
    | _, _ => h := update h (List.replicate 32 0)
  else
    h := update h (List.replicate 32 0)
  h := update h (digests.joinsplits.getD (List.replicate 32 0))
  if tx.version.hasSapling then
    h := update h (digests.saplingSpends.getD (List.replicate 32 0))
    h := update h (digests.saplingOutputs.getD (List.replicate 32 0))
  h := update h (toLeBytes 4 tx.lockTime)
  h := update h (toLeBytes 4 tx.expiryHeight)
  if tx.version.hasSapling then
    h := update h (toLeBytes 8 tx.saplingValueBalance)
  h := update h (toLeBytes 4 (hashType.setWidth 32))
  match signableInput with
  | .shielded => pure ()
  | .transparent input =>
    match tx.transparentBundle with
    | some bundle =>
      let txin ← bundle.vin[input.index]?
      let data ← unwrap (txin.prevout.write ([] : VecU8))
      let data ← unwrap (input.scriptCode.write data)
      let data := data ++ toLeBytes 8 input.value
      let data := data ++ toLeBytes 4 txin.sequence
      h := update h data
    | none => none
  pure (finalize h)

end ZcashSighash.Verifier
