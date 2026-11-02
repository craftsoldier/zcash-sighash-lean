/-
Zebra 7.0.0's signature digests (`zebra-chain` 15.0.0, `src/primitives/zcash_primitives.rs` and
`src/transaction/compat.rs`), and the `zcash_primitives` 0.31.0 code they call that the digests
do not: `TransactionData::from_parts`, `from_parts_v6` and `map_authorization`
(`src/transaction/mod.rs`), with the `map_authorization` of `zcash_transparent` 0.11.0,
`sapling-crypto` 0.9.0 and `orchard` 0.16.0, and `PrecomputedSighashData::new`
(`src/transaction/sighash.rs`).

Zebra does not hash the transaction `Transaction::read` returned: it takes it apart, rebuilds it
with the consensus branch ID of the network upgrade it validates it under, and replaces its
transparent authorization with the coins its inputs spend (`all_previous_outputs`).
-/
module

public import ZcashSighash.Verifier.SighashV4
public import ZcashSighash.Verifier.Parse

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes)

/-! ## `map_authorization` -/

/-- `MapAuth` (`zcash_transparent`, `src/bundle.rs`, lines 61–64). -/
structure Transparent.MapAuth where
  mapScriptSig : Transparent.Script → Transparent.Script
  mapAuthorization : Transparent.AuthorizingContext → Transparent.AuthorizingContext

/-- `Bundle::map_authorization` (lines 101–117). -/
def Transparent.Bundle.mapAuthorization (self : Transparent.Bundle) (f : Transparent.MapAuth) :
    Transparent.Bundle where
  vin := self.vin.map fun txin => ⟨txin.prevout, f.mapScriptSig txin.scriptSig, txin.sequence⟩
  vout := self.vout
  authorization := f.mapAuthorization self.authorization

/-- `MapAuth` (`zcash_primitives`, `src/transaction/components/sapling.rs`, lines 102–107): a
    spend proof, an output proof, a spend authorization signature, and the bundle's
    authorization, `Authorized`'s binding signature (`sapling-crypto`, `src/bundle.rs`, lines
    45–48). -/
structure Sapling.MapAuth where
  mapSpendProof : Bytes 192 → Bytes 192
  mapOutputProof : Bytes 192 → Bytes 192
  mapAuthSig : Bytes 64 → Bytes 64
  mapAuthorization : Bytes 64 → Bytes 64

/-- `Bundle::map_authorization` (`sapling-crypto`, `src/bundle.rs`, lines 109–145), with the
    closures `TransactionData::map_authorization` passes (`src/transaction/mod.rs`, lines
    848–856), each calling the `MapAuth` method of its name. -/
def Sapling.Bundle.mapAuthorization (self : Sapling.Bundle) (f : Sapling.MapAuth) :
    Sapling.Bundle where
  shieldedSpends := self.shieldedSpends.map fun d =>
    ⟨d.cv, d.anchor, d.nullifier, d.rk, f.mapSpendProof d.zkproof, f.mapAuthSig d.spendAuthSig⟩
  shieldedOutputs := self.shieldedOutputs.map fun o =>
    ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, f.mapOutputProof o.zkproof⟩
  valueBalance := self.valueBalance
  bindingSig := f.mapAuthorization self.bindingSig

/-- `MapAuth` (`zcash_primitives`, `src/transaction/components/orchard.rs`, lines 81–84): an
    Action's spend authorization signature, and the bundle's authorization, `Authorized`'s proof
    and binding signature (`orchard`, `src/bundle.rs`, lines 824–827). -/
structure Orchard.MapAuth where
  mapSpendAuth : Bytes 64 → Bytes 64
  mapAuthorization : List Byte × Bytes 64 → List Byte × Bytes 64

/-- `Bundle::map_authorization` (`orchard`, `src/bundle.rs`, lines 608–625), through
    `Action::map` (`src/action.rs`, lines 121–130), with the closures
    `TransactionData::map_authorization` passes (`src/transaction/mod.rs`, lines 857–870). The
    action closure ignores the bundle's authorization it is passed. -/
def Orchard.Bundle.mapAuthorization (self : Orchard.Bundle) (f : Orchard.MapAuth) :
    Orchard.Bundle :=
  let authorization := (self.proof, self.bindingSignature)
  let actions : Orchard.NonEmpty Orchard.Action :=
    ⟨mapAction self.actions.head, self.actions.tail.map mapAction⟩
  let authorization := f.mapAuthorization authorization
  { actions := actions
    flagByte := self.flagByte
    valueBalance := self.valueBalance
    anchor := self.anchor
    proof := authorization.1
    bindingSignature := authorization.2
    valuePool := self.valuePool }
where
  /-- `Action::map` with `f`'s `map_spend_auth`. -/
  mapAction (a : Orchard.Action) : Orchard.Action :=
    ⟨a.nf, a.rk, a.cmx, a.epkBytes, a.encCiphertext, a.outCiphertext, a.cvNet,
      f.mapSpendAuth a.authorization⟩

/-! ## `zcash_primitives` 0.31.0, `src/transaction/mod.rs` -/

/-- `TransactionData::from_parts` (lines 386–409): no Ironwood bundle. -/
def TransactionData.fromParts (version : TxVersion) (consensusBranchId lockTime expiryHeight :
    BitVec 32) (transparentBundle : Option Transparent.Bundle)
    (sproutBundle : Option Sprout.Bundle) (saplingBundle : Option Sapling.Bundle)
    (orchardBundle : Option Orchard.Bundle) : TransactionData :=
  ⟨version, consensusBranchId, lockTime, expiryHeight, transparentBundle, sproutBundle,
    saplingBundle, orchardBundle, none⟩

/-- `TransactionData::from_parts_v6` (lines 455–474), through `from_parts_v6_or_v7` (lines
    563–592): version 6, no Sprout bundle. Its `debug_assert!` is skipped: the model is a release
    build. -/
def TransactionData.fromPartsV6 (consensusBranchId lockTime expiryHeight : BitVec 32)
    (transparentBundle : Option Transparent.Bundle) (saplingBundle : Option Sapling.Bundle)
    (orchardBundle ironwoodBundle : Option Orchard.Bundle) : TransactionData :=
  ⟨.v6, consensusBranchId, lockTime, expiryHeight, transparentBundle, none, saplingBundle,
    orchardBundle, ironwoodBundle⟩

/-- `TransactionData::map_authorization` (lines 831–872): the Orchard map is applied to the
    Ironwood bundle too. -/
def TransactionData.mapAuthorization (self : TransactionData) (fTransparent : Transparent.MapAuth)
    (fSapling : Sapling.MapAuth) (fOrchard : Orchard.MapAuth) : TransactionData where
  version := self.version
  consensusBranchId := self.consensusBranchId
  lockTime := self.lockTime
  expiryHeight := self.expiryHeight
  transparentBundle := self.transparentBundle.map (·.mapAuthorization fTransparent)
  sproutBundle := self.sproutBundle
  saplingBundle := self.saplingBundle.map (·.mapAuthorization fSapling)
  orchardBundle := self.orchardBundle.map (·.mapAuthorization fOrchard)
  ironwoodBundle := self.ironwoodBundle.map (·.mapAuthorization fOrchard)

/-! ## `zcash_primitives` 0.31.0, `src/transaction/sighash.rs` -/

/-- `PrecomputedSighashData` (lines 46–53), with either kind of `TxDigests`: ZIP 143's, with the
    transaction, or ZIP 244's, which `PrecomputedSighashData` holds. -/
inductive Precomputed where
  | zip143 (tx : TransactionData) (digests : Zip143Digests)
  | zip244 (data : PrecomputedSighashData)

/-- `PrecomputedSighashData::new` (lines 62–72), through `from_tx_digests` (lines 107–120),
    which computes no transparent input digests for ZIP 143. -/
def PrecomputedSighashData.new (tx : TransactionData) : Option Precomputed := do
  match tx.version with
  | .sprout _ | .v3 | .v4 => pure (.zip143 tx (← zip143Digests tx))
  | .v5 | .v6 =>
    let txDigests ← tx.txIdDigests
    let transparentInputsDigests ← match tx.transparentBundle with
      | none => pure none
      | some b => TransparentInputsDigests.forBundle b
    pure (.zip244 ⟨tx, txDigests, transparentInputsDigests⟩)

/-- `PrecomputedSighashData::tx` (lines 123–125). -/
def Precomputed.tx : Precomputed → TransactionData
  | .zip143 tx _ => tx
  | .zip244 data => data.tx

/-- `PrecomputedSighashData::signature_hash` (lines 148–159): `v4_signature_hash` with ZIP 143
    digests, and otherwise as for ZIP 244. -/
def Precomputed.signatureHash (self : Precomputed) (signableInput : SignableInput) :
    Option Blake2bHash :=
  match self with
  | .zip143 tx digests => v4SignatureHash tx signableInput digests
  | .zip244 data => data.signatureHash signableInput

/-! ## `zebra-chain` 15.0.0 -/

namespace Zebra

/-- `Transaction::version` (`src/transaction.rs`, lines 81–91). Its `panic!` is unreachable:
    without `zcash_unstable = "nutachyon"`, `TxVersion` has no other variant. -/
def version : TxVersion → ℕ
  | .sprout v => v.toNat
  | .v3 => 3
  | .v4 => 4
  | .v5 => 5
  | .v6 => 6

/-- `transparent::Output` (`src/transparent.rs`, lines 330–337): its value an
    `Amount<NonNegative>`, which holds an `i64` in `0..=MAX_MONEY` (`src/amount.rs`, lines
    580–584; `MAX_MONEY`, line 610, the same value as `Native.MAX_MONEY`), and its lock
    script. -/
structure Output where
  value : BitVec 64
  lockScript : Transparent.Script
  value_le : value.toNat ≤ Native.MAX_MONEY

/-- `TransparentAuth` (`src/primitives/zcash_primitives.rs`, lines 24–27), as the
    `TransparentAuthorizingContext` it implements (lines 35–58): the values and lock scripts of
    `all_prev_outputs`. A value in `0..=MAX_MONEY` is a valid `Zatoshis`, so its
    `try_into().expect(...)` (lines 40–43) cannot panic. -/
def transparentAuth (allPrevOutputs : List Output) : Transparent.AuthorizingContext :=
  ⟨allPrevOutputs.map (·.value), allPrevOutputs.map (·.lockScript)⟩

/-- `MapTransparent` (lines 64–82): each `scriptSig` kept, the authorization replaced. -/
def mapTransparent (auth : Transparent.AuthorizingContext) : Transparent.MapAuth :=
  ⟨fun s => s, fun _ => auth⟩

/-- `IdentityMap`'s Sapling `MapAuth` (lines 86–122): each argument returned. -/
def identityMapSapling : Sapling.MapAuth := ⟨fun p => p, fun p => p, fun s => s, fun a => a⟩

/-- `IdentityMap`'s Orchard `MapAuth` (lines 124–137): each argument returned. -/
def identityMapOrchard : Orchard.MapAuth := ⟨fun s => s, fun a => a⟩

/-- `transaction_data_from_parts` (`src/transaction/compat.rs`, lines 293–332): `from_parts_v6`
    for version 6, which drops the Sprout bundle, and `from_parts` otherwise, which drops the
    Ironwood bundle. Its `debug_assert!` (lines 316–319) is skipped: the model is a release
    build. -/
def transactionDataFromParts (version : TxVersion) (branchId lockTime expiryHeight : BitVec 32)
    (transparentBundle : Option Transparent.Bundle) (sproutBundle : Option Sprout.Bundle)
    (saplingBundle : Option Sapling.Bundle) (orchardBundle ironwoodBundle : Option Orchard.Bundle) :
    TransactionData :=
  match version with
  | .v6 => TransactionData.fromPartsV6 branchId lockTime expiryHeight transparentBundle
      saplingBundle orchardBundle ironwoodBundle
  | _ => TransactionData.fromParts version branchId lockTime expiryHeight transparentBundle
      sproutBundle saplingBundle orchardBundle

/-- `PrecomputedTxData` (`src/primitives/zcash_primitives.rs`, lines 212–220). -/
structure PrecomputedTxData where
  sighashData : Precomputed
  allPreviousOutputs : List Output

/-- `PrecomputedTxData::from_transaction_with_branch_id` (lines 252–296): the transaction rebuilt
    with `branch_id`, and its transparent authorization replaced by `all_previous_outputs`'. -/
def fromTransactionWithBranchId (tx : TransactionData) (branchId : BitVec 32)
    (allPreviousOutputs : List Output) : Option PrecomputedTxData := do
  let data := tx
  let dataWithBranchId := transactionDataFromParts data.version branchId data.lockTime
    data.expiryHeight data.transparentBundle data.sproutBundle data.saplingBundle
    data.orchardBundle data.ironwoodBundle
  let txData := dataWithBranchId.mapAuthorization
    (mapTransparent (transparentAuth allPreviousOutputs)) identityMapSapling identityMapOrchard
  pure ⟨← PrecomputedSighashData.new txData, allPreviousOutputs⟩

/-- `Error` (`src/error.rs`, lines 62–82), the variant `PrecomputedTxData::new` returns. -/
inductive Error where
  | invalidConsensusBranchId

/-- `PrecomputedTxData::new` (`src/primitives/zcash_primitives.rs`, lines 228–246). `nuBranchId`
    is the network upgrade's consensus branch ID, if it has one that `BranchId::try_from` accepts
    (lines 233–236). From version 5 on, it must be the transaction's own. -/
def PrecomputedTxData.new (tx : TransactionData) (nuBranchId : Option (BitVec 32))
    (allPreviousOutputs : List Output) : Option (Except Error PrecomputedTxData) :=
  match nuBranchId with
  | none => pure (.error .invalidConsensusBranchId)
  | some branchId =>
    let txBranchId := tx.consensusBranchId
    if version tx.version ≥ 5 ∧ txBranchId ≠ branchId then pure (.error .invalidConsensusBranchId)
    else Except.ok <$> fromTransactionWithBranchId tx branchId allPreviousOutputs

/-- `SighashError` (lines 332–360), without `InvalidPreviousOutputAmount`, which `sighash_inner`
    never returns. -/
inductive SighashError where
  | inputIndexOutOfBounds
  | noTransparentBundle
  | bundleInputCountMismatch

/-- `sighash_inner` (lines 467–531): the signable input, then `signature_hash`. A previous output's
    value is a valid `Zatoshis`, as in `transparentAuth`, so `InvalidPreviousOutputAmount` (lines
    503–506) is never returned. -/
def sighashInner (precomputedTxData : PrecomputedTxData) (sighashType : Transparent.SighashType)
    (inputIndexScriptCode : Option (ℕ × List Byte)) :
    Option (Except SighashError Blake2bHash) := do
  let signableInput : Except SighashError SignableInput := match inputIndexScriptCode with
    | some (inputIndex, scriptCode) =>
      match precomputedTxData.allPreviousOutputs[inputIndex]? with
      | none => .error .inputIndexOutOfBounds
      | some output =>
        match precomputedTxData.sighashData.tx.transparentBundle with
        | none => .error .noTransparentBundle
        | some bundle =>
          let lockScript := output.lockScript
          let unlockScript : Transparent.Script := ⟨scriptCode⟩
          let value := output.value
          match Transparent.SignableInput.fromParts bundle sighashType inputIndex unlockScript
              lockScript value with
          | .error _ => .error .bundleInputCountMismatch
          | .ok fromParts => .ok (.transparent fromParts)
    | none => .ok .shielded
  match signableInput with
  | .error e => pure (.error e)
  | .ok signableInput => Except.ok <$> precomputedTxData.sighashData.signatureHash signableInput

/-- `HashType` (`src/transaction/sighash.rs`, lines 15–35), its bits, as
    `SighashType::try_from` converts it (lines 37–51): the six hash types it names, and an error
    for any other. -/
def toSighashType? (hashType : BitVec 32) : Option Transparent.SighashType :=
  if hashType = 0x01 then some ⟨Transparent.SIGHASH_ALL⟩
  else if hashType = 0x02 then some ⟨Transparent.SIGHASH_NONE⟩
  else if hashType = 0x03 then some ⟨Transparent.SIGHASH_SINGLE⟩
  else if hashType = 0x81 then some ⟨Transparent.SIGHASH_ALL ||| Transparent.SIGHASH_ANYONECANPAY⟩
  else if hashType = 0x82 then some ⟨Transparent.SIGHASH_NONE ||| Transparent.SIGHASH_ANYONECANPAY⟩
  else if hashType = 0x83 then
    some ⟨Transparent.SIGHASH_SINGLE ||| Transparent.SIGHASH_ANYONECANPAY⟩
  else none

/-- `sighash` (`src/primitives/zcash_primitives.rs`, lines 418–433): both `expect`s panic, on a
    hash type `SighashType::try_from` rejects and on a `SighashError`. -/
def sighash (precomputedTxData : PrecomputedTxData) (hashType : BitVec 32)
    (inputIndexScriptCode : Option (ℕ × List Byte)) : Option Blake2bHash := do
  match ← sighashInner precomputedTxData (← toSighashType? hashType) inputIndexScriptCode with
  | .ok sigHash => pure sigHash
  | .error _ => none

/-- `sighash_v4_raw` (lines 444–459), with `SighashType::from_raw` (`zcash_transparent`,
    `src/sighash.rs`, lines 43–45), which keeps the byte. -/
def sighashV4Raw (precomputedTxData : PrecomputedTxData) (rawHashType : Byte)
    (inputIndexScriptCode : Option (ℕ × List Byte)) : Option Blake2bHash := do
  match ← sighashInner precomputedTxData ⟨rawHashType⟩ inputIndexScriptCode with
  | .ok sigHash => pure sigHash
  | .error _ => none

end Zebra

end ZcashSighash.Verifier
