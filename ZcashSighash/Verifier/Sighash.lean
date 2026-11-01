/-
`zcash_primitives` 0.31.0's version 5 and 6 signature digests (`src/transaction/sighash_v5.rs`,
`sighash_v6.rs`, `sighash.rs`). Version 4 and earlier (ZIP 143, ZIP 243) are out of scope.
-/
module

public import ZcashSighash.Verifier.TxId

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)
open Transparent (SIGHASH_ALL SIGHASH_ANYONECANPAY SIGHASH_MASK SIGHASH_NONE SIGHASH_SINGLE)

/-- `SignableInput` (`src/transaction/sighash.rs`, lines 16–19). -/
inductive SignableInput where
  | shielded
  | transparent (input : Transparent.SignableInput)

/-- `SignableInput::hash_type` (lines 22–27). -/
def SignableInput.hashType : SignableInput → Byte
  | .shielded => SIGHASH_ALL
  | .transparent input => input.hashType.encode

/-! ## `src/transaction/sighash_v5.rs` -/

/-- `TransparentInputsDigests` (lines 38–41). -/
structure TransparentInputsDigests where
  amounts : Blake2bHash
  scripts : Blake2bHash

/-- `TransparentInputsDigests::new` (lines 46–67). Writing a `scriptPubKey` longer than
    `MAX_COMPACT_SIZE` fails, and the `unwrap` panics. -/
def TransparentInputsDigests.new (bundle : Transparent.Bundle) :
    Option TransparentInputsDigests := do
  let amounts ← hasher (personal "ZTxTrAmountsHash")
  let amounts ← unwrap (Array.write amounts bundle.authorization.inputAmounts
    fun w amount => w.writeAll (toLeBytes 8 amount))
  let scripts ← hasher (personal "ZTxTrScriptsHash")
  let scripts ← unwrap (Array.write scripts bundle.authorization.inputScriptpubkeys
    fun w script => script.write w)
  pure ⟨amounts.finalize, scripts.finalize⟩

/-- `TransparentInputsDigests::for_bundle` (lines 75–79). -/
def TransparentInputsDigests.forBundle (bundle : Transparent.Bundle) :
    Option (Option TransparentInputsDigests) :=
  if !bundle.isCoinbase && !bundle.vin.isEmpty then some <$> TransparentInputsDigests.new bundle
  else pure none

/-- `transparent_sig_digest` (lines 87–174). `bundle.vin[*input.index()]` panics for an index out
    of range, which `SignableInput::from_parts` rules out only for the bundle it was given. -/
def transparentSigDigest (txData : Option (Transparent.Bundle × TransparentDigests))
    (inputsDigests : Option TransparentInputsDigests) (input : SignableInput) :
    Option Blake2bHash :=
  match txData with
  | none => hashTransparentTxidData none
  | some (bundle, txidDigests) =>
    if bundle.isCoinbase || bundle.vin.isEmpty then hashTransparentTxidData (some txidDigests)
    else do
      let hashType := input.hashType
      let flagAnyonecanpay := hashType &&& SIGHASH_ANYONECANPAY != 0
      let flagSingle := hashType &&& SIGHASH_MASK == SIGHASH_SINGLE
      let flagNone := hashType &&& SIGHASH_MASK == SIGHASH_NONE
      let prevoutsDigest ← if flagAnyonecanpay then transparentPrevoutHash []
        else pure txidDigests.prevoutsDigest
      let (amountsDigest, scriptsDigest) ← if flagAnyonecanpay then do
          pure ((← hasher (personal "ZTxTrAmountsHash")).finalize,
            (← hasher (personal "ZTxTrScriptsHash")).finalize)
        else match inputsDigests with
          | some digests => pure (digests.amounts, digests.scripts)
          | none => do
            let digests ← TransparentInputsDigests.new bundle
            pure (digests.amounts, digests.scripts)
      let sequenceDigest ← if flagAnyonecanpay then transparentSequenceHash []
        else pure txidDigests.sequenceDigest
      let outputsDigest ← match input with
        | .transparent input =>
          if flagSingle then
            if input.index < bundle.vout.length then
              transparentOutputsHash [← bundle.vout[input.index]?]
            else transparentOutputsHash []
          else if flagNone then transparentOutputsHash []
          else pure txidDigests.outputsDigest
        | .shielded => pure txidDigests.outputsDigest
      let mut ch ← hasher (personal "Zcash___TxInHash")
      if let .transparent input := input then
        let txin ← bundle.vin[input.index]?
        ch ← unwrap (txin.prevout.write ch)
        ch ← unwrap (ch.writeAll (toLeBytes 8 input.value))
        ch ← unwrap (input.scriptPubkey.write ch)
        ch ← unwrap (ch.writeAll (toLeBytes 4 txin.sequence))
      let txinSigDigest := ch.finalize
      let mut h ← hasher (personal "ZTxIdTranspaHash")
      h ← unwrap (h.writeAll [hashType])
      h ← unwrap (h.writeAll prevoutsDigest)
      h ← unwrap (h.writeAll amountsDigest)
      h ← unwrap (h.writeAll scriptsDigest)
      h ← unwrap (h.writeAll sequenceDigest)
      h ← unwrap (h.writeAll outputsDigest)
      h ← unwrap (h.writeAll txinSigDigest)
      pure h.finalize

/-- `Option::zip`. -/
def zipOption {α β : Type} : Option α → Option β → Option (α × β)
  | some a, some b => some (a, b)
  | _, _ => none

/-- `v5_signature_hash` (lines 178–208): a panic if the transparent digests are given exactly
    when there is no transparent bundle. -/
def v5SignatureHash (tx : TransactionData) (signableInput : SignableInput)
    (txidParts : Zip244Digests) (inputsDigests : Option TransparentInputsDigests) :
    Option Blake2bHash := do
  guard (tx.transparentBundle.isSome = txidParts.transparentDigests.isSome)
  toHash tx.version tx.consensusBranchId txidParts.headerDigest
    (← transparentSigDigest (zipOption tx.transparentBundle txidParts.transparentDigests)
      inputsDigests signableInput)
    txidParts.saplingDigest txidParts.orchardDigest

/-- `v6_signature_hash` (`src/transaction/sighash_v6.rs`, lines 14–44). -/
def v6SignatureHash (tx : TransactionData) (signableInput : SignableInput)
    (txidParts : Zip244Digests) (inputsDigests : Option TransparentInputsDigests) :
    Option Blake2bHash := do
  guard (tx.transparentBundle.isSome = txidParts.transparentDigests.isSome)
  toHashV6 tx.consensusBranchId txidParts.headerDigest
    (← transparentSigDigest (zipOption tx.transparentBundle txidParts.transparentDigests)
      inputsDigests signableInput)
    txidParts.saplingDigest txidParts.orchardDigest txidParts.ironwoodDigest

/-! ## `src/transaction/sighash.rs` -/

/-- `PrecomputedSighashData` (lines 46–53), with ZIP 244 digests: `new_zip244` builds no other. -/
structure PrecomputedSighashData where
  tx : TransactionData
  txDigests : Zip244Digests
  transparentInputsDigests : Option TransparentInputsDigests

/-- `PrecomputedSighashData::new_zip244` (lines 88–103), through `from_tx_digests` (lines
    107–120): `none` (the inner one) for a version before 5, `Zip244Error::NotZip244`. -/
def PrecomputedSighashData.newZip244 (tx : TransactionData) :
    Option (Option PrecomputedSighashData) := do
  match tx.version with
  | .sprout _ | .v3 | .v4 => pure none
  | .v5 | .v6 =>
    let txDigests ← tx.txIdDigests
    let transparentInputsDigests ← match tx.transparentBundle with
      | none => pure none
      | some b => TransparentInputsDigests.forBundle b
    pure (some ⟨tx, txDigests, transparentInputsDigests⟩)

/-- `PrecomputedSighashData::signature_hash` (lines 148–159). -/
def PrecomputedSighashData.signatureHash (self : PrecomputedSighashData)
    (signableInput : SignableInput) : Option Blake2bHash :=
  if self.tx.version.hasIronwood then
    v6SignatureHash self.tx signableInput self.txDigests self.transparentInputsDigests
  else v5SignatureHash self.tx signableInput self.txDigests self.transparentInputsDigests

end ZcashSighash.Verifier
