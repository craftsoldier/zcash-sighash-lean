/-
Zakura's digests: `zakura-primitives` 4.0.0 (`src/transaction/`), with `zakura-transparent`
4.0.0, `zakura-protocol` 4.0.0's `encoding` module, `zakura-orchard` 4.0.0 and
`zakura-sapling-crypto` 4.0.0. Zakura forked librustzcash; where its code is the text of
`zcash_primitives` 0.31.0's (or reads the same bytes: `zakura-orchard`'s commitments index the
ciphertext array directly, and `zakura-sapling-crypto`'s `OutputDescription` holds the
ciphertext as a `[u8; 580]`, `src/bundle.rs`, lines 295–302) and calls nothing that differs, the
Lean reuses that transcription. What follows is what differs:

* `CompactSize::write` has no `MAX_COMPACT_SIZE` bound, so the writers above it differ: `Vector`,
  `Script`, `TxOut`, and each digest that writes a script.
* The signature digests compute every component digest when called: there is no precomputed
  `TransparentInputsDigests` or `Zip143Digests`.
* `to_txid` has no version check, and `signature_hash` dispatches on the version.

The data types (`TransactionData`, `TxDigests` as `Zip244Digests`, the bundles, `SignableInput`)
have the same fields as librustzcash's.
-/
module

public import ZcashSighash.Verifier.SighashV4

@[expose] public section

namespace ZcashSighash.Verifier.Zakura

open Spec (Byte Bytes personal)
open Transparent (SIGHASH_ANYONECANPAY SIGHASH_MASK SIGHASH_NONE SIGHASH_SINGLE)
open Orchard (update finalize)

/-! ## `zakura-protocol` 4.0.0, `src/encoding.rs` -/

/-- `CompactSize::write` (lines 96–112): any size. A `usize` fits in a `u64`, so `s as u64` keeps
    `s`. -/
def CompactSize.write {W : Type} [Write W] (writer : W) (size : ℕ) : IoResult W :=
  if size < 253 then Write.writeAll writer [BitVec.ofNat 8 size]
  else if size ≤ 0xFFFF then do
    let writer ← Write.writeAll writer [253]
    Write.writeAll writer (toLeBytes 2 (BitVec.ofNat 16 size))
  else if size ≤ 0xFFFFFFFF then do
    let writer ← Write.writeAll writer [254]
    Write.writeAll writer (toLeBytes 4 (BitVec.ofNat 32 size))
  else do
    let writer ← Write.writeAll writer [255]
    Write.writeAll writer (toLeBytes 8 (BitVec.ofNat 64 size))

/-- `Vector::write` (lines 166–171), through `Vector::write_sized` (lines 190–200). -/
def Vector.write {W E : Type} [Write W] (writer : W) (vec : List E)
    (func : W → E → IoResult W) : IoResult W := do
  let writer ← CompactSize.write writer vec.length
  vec.foldlM func writer

/-! ## `zakura-transparent` 4.0.0 -/

/-- `Script::write` (`src/address.rs`, lines 71–73). -/
def Script.write {W : Type} [Write W] (self : Transparent.Script) (writer : W) : IoResult W :=
  Vector.write writer self.code fun w e => Write.writeAll w [e]

/-- `TxOut::write` (`src/bundle.rs`, lines 400–403). -/
def TxOut.write {W : Type} [Write W] (self : Transparent.TxOut) (writer : W) : IoResult W := do
  let writer ← Write.writeAll writer (toLeBytes 8 self.value)
  Script.write self.scriptPubkey writer

/-! ## `zakura-primitives` 4.0.0, `src/transaction/txid.rs` -/

/-- `transparent_outputs_hash` (lines 130–136). -/
def transparentOutputsHash (vout : List Transparent.TxOut) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdOutputsHash")
  for tOut in vout do
    h ← unwrap (TxOut.write tOut h)
  pure h.finalize

/-- `transparent_digests` (lines 215–223). -/
def transparentDigests (bundle : Transparent.Bundle) : Option TransparentDigests := do
  pure ⟨← transparentPrevoutHash bundle.vin, ← transparentSequenceHash bundle.vin,
    ← transparentOutputsHash bundle.vout⟩

/-- `TransactionData::digest` (`mod.rs`, lines 485–498) with `TxIdDigester` (`txid.rs`, lines
    291–366): as librustzcash's, but for the transparent digests. -/
def TransactionData.txIdDigests (self : TransactionData) : Option Zip244Digests := do
  let headerDigest ← hashHeaderTxidData self.version self.consensusBranchId self.lockTime
    self.expiryHeight
  let transparentDigests ← match self.transparentBundle with
    | none => pure none
    | some b => some <$> transparentDigests b
  let saplingDigest ← match self.saplingBundle with
    | none => pure none
    | some b => some <$> hashSaplingTxidData self.version b
  let orchardDigest ← TxIdDigester.digestOrchard self.version self.orchardBundle
  let ironwoodDigest ← TxIdDigester.digestIronwood self.ironwoodBundle
  pure ⟨headerDigest, transparentDigests, saplingDigest, orchardDigest, ironwoodDigest⟩

/-- `to_txid` (lines 457–483): no version check. -/
def toTxid (txversion : TxVersion) (consensusBranchId : BitVec 32) (digests : Zip244Digests) :
    Option Blake2bHash :=
  if txversion.hasIronwood then do
    toHashV6 consensusBranchId digests.headerDigest
      (← hashTransparentTxidData digests.transparentDigests) digests.saplingDigest
      digests.orchardDigest digests.ironwoodDigest
  else do
    toHash txversion consensusBranchId digests.headerDigest
      (← hashTransparentTxidData digests.transparentDigests) digests.saplingDigest
      digests.orchardDigest

/-- `BlockTxCommitmentDigester::digest_transparent` (lines 513–524). -/
def digestTransparent (transparentBundle : Option Transparent.Bundle) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxAuthTransHash")
  if let some bundle := transparentBundle then
    for txin in bundle.vin do
      h ← unwrap (Script.write txin.scriptSig h)
  pure h.finalize

/-- `Transaction::auth_commitment` (`mod.rs`, lines 1025–1027): `TransactionData::digest` with
    `BlockTxCommitmentDigester` (`txid.rs`, lines 491–620), as librustzcash's but for the
    transparent digest. -/
def TransactionData.authCommitment (self : TransactionData) : Option Blake2bHash := do
  let transparentDigest ← digestTransparent self.transparentBundle
  let saplingDigest ← BlockTxCommitmentDigester.digestSapling self.version self.saplingBundle
  let orchardDigest ← BlockTxCommitmentDigester.digestOrchard self.version self.orchardBundle
  let ironwoodDigest ← BlockTxCommitmentDigester.digestIronwood self.ironwoodBundle
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZTxAuthHash_" 12)
    self.consensusBranchId)
  h ← unwrap (h.writeAll transparentDigest)
  h ← unwrap (h.writeAll saplingDigest)
  h ← unwrap (h.writeAll orchardDigest)
  if self.version.hasIronwood then
    h ← unwrap (h.writeAll ironwoodDigest)
  pure h.finalize

/-! ## `src/transaction/sighash_v5.rs`, `sighash_v6.rs`, `sighash.rs` -/

/-- `transparent_sig_digest` (`sighash_v5.rs`, lines 34–129): the amounts and `scriptPubKey`s
    digests computed on every call. -/
def transparentSigDigest (txData : Option (Transparent.Bundle × TransparentDigests))
    (input : SignableInput) : Option Blake2bHash :=
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
      let mut ha ← hasher (personal "ZTxTrAmountsHash")
      if !flagAnyonecanpay then
        ha ← unwrap (Array.write ha bundle.authorization.inputAmounts
          fun w amount => w.writeAll (toLeBytes 8 amount))
      let amountsDigest := ha.finalize
      let mut hs ← hasher (personal "ZTxTrScriptsHash")
      if !flagAnyonecanpay then
        hs ← unwrap (Array.write hs bundle.authorization.inputScriptpubkeys
          fun w script => Script.write script w)
      let scriptsDigest := hs.finalize
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
        ch ← unwrap (Script.write input.scriptPubkey ch)
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

/-- `v5_signature_hash` (`sighash_v5.rs`, lines 132–160). -/
def v5SignatureHash (tx : TransactionData) (signableInput : SignableInput)
    (txidParts : Zip244Digests) : Option Blake2bHash := do
  guard (tx.transparentBundle.isSome = txidParts.transparentDigests.isSome)
  toHash tx.version tx.consensusBranchId txidParts.headerDigest
    (← transparentSigDigest (zipOption tx.transparentBundle txidParts.transparentDigests)
      signableInput)
    txidParts.saplingDigest txidParts.orchardDigest

/-- `v6_signature_hash` (`sighash_v6.rs`, lines 10–38). -/
def v6SignatureHash (tx : TransactionData) (signableInput : SignableInput)
    (txidParts : Zip244Digests) : Option Blake2bHash := do
  guard (tx.transparentBundle.isSome = txidParts.transparentDigests.isSome)
  toHashV6 tx.consensusBranchId txidParts.headerDigest
    (← transparentSigDigest (zipOption tx.transparentBundle txidParts.transparentDigests)
      signableInput)
    txidParts.saplingDigest txidParts.orchardDigest txidParts.ironwoodDigest

/-! ## `src/transaction/sighash_v4.rs` -/

/-- `outputs_hash` (lines 58–67). -/
def outputsHash (vout : List Transparent.TxOut) : Option Blake2bHash := do
  let mut data : VecU8 := []
  for tOut in vout do
    data ← unwrap (TxOut.write tOut data)
  hashWith (personal "ZcashOutputsHash") data

/-- `single_output_hash` (lines 69–76). -/
def singleOutputHash (txOut : Transparent.TxOut) : Option Blake2bHash := do
  let data ← unwrap (TxOut.write txOut ([] : VecU8))
  hashWith (personal "ZcashOutputsHash") data

/-- `update_hash!` (lines 26–34): the value, computed only when `cond` holds, or 32 zero bytes. -/
def updateHashLazy (h : Blake2b.State) (cond : Bool) (value : Unit → Option Blake2bHash) :
    Option Blake2b.State :=
  if cond then do pure (update h (← value ())) else pure (update h (List.replicate 32 0))

/-- `Option::is_none_or`. -/
def isNoneOr {α : Type} (o : Option α) (p : α → Bool) : Bool :=
  match o with
  | none => true
  | some a => p a

/-- `v4_signature_hash` (lines 131–257): every component digest computed here, through
    `update_hash!`. A panic for a version before Overwinter, and for a transparent input without a
    transparent bundle or out of its range; the `unwrap`s inside `update_hash!` are evaluated only
    when the bundle is there. -/
def v4SignatureHash (tx : TransactionData) (signableInput : SignableInput) :
    Option Blake2bHash := do
  let hashType := signableInput.hashType
  if !tx.version.hasOverwinter then none
  let params ← Blake2b.Params.new.hashLength? 32
  let params ← params.personal?
    ((branchPersonalization (Spec.ascii "ZcashSigHash" 12) tx.consensusBranchId).toList.map
      (·.toNat))
  let vin := (tx.transparentBundle.map (·.vin)).getD []
  let vout := (tx.transparentBundle.map (·.vout)).getD []
  let mut h := params.toState
  h := update h (toLeBytes 4 tx.version.header)
  h := update h (toLeBytes 4 tx.version.versionGroupId)
  h ← updateHashLazy h (hashType &&& SIGHASH_ANYONECANPAY == 0) fun _ => prevoutHash vin
  h ← updateHashLazy h (hashType &&& SIGHASH_ANYONECANPAY == 0 &&
      hashType &&& SIGHASH_MASK != SIGHASH_SINGLE && hashType &&& SIGHASH_MASK != SIGHASH_NONE)
    fun _ => sequenceHash vin
  if hashType &&& SIGHASH_MASK != SIGHASH_SINGLE && hashType &&& SIGHASH_MASK != SIGHASH_NONE then
    h := update h (← outputsHash vout)
  else if hashType &&& SIGHASH_MASK == SIGHASH_SINGLE then
    match tx.transparentBundle, signableInput with
    | some b, .transparent input =>
      if input.index < b.vout.length then
        h := update h (← singleOutputHash (← b.vout[input.index]?))
      else h := update h (List.replicate 32 0)
    | _, _ => h := update h (List.replicate 32 0)
  else
    h := update h (List.replicate 32 0)
  h ← updateHashLazy h (!isNoneOr tx.sproutBundle (·.joinsplits.isEmpty)) fun _ => do
    let bundle ← tx.sproutBundle
    joinsplitsHash bundle.joinsplits bundle.joinsplitPubkey
  if tx.version.hasSapling then
    h ← updateHashLazy h (!isNoneOr tx.saplingBundle (·.shieldedSpends.isEmpty)) fun _ => do
      saplingSpendsHash (← tx.saplingBundle).shieldedSpends
    h ← updateHashLazy h (!isNoneOr tx.saplingBundle (·.shieldedOutputs.isEmpty)) fun _ => do
      saplingOutputsHash (← tx.saplingBundle).shieldedOutputs
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
      let data ← unwrap (Script.write input.scriptCode data)
      let data := data ++ toLeBytes 8 input.value
      let data := data ++ toLeBytes 4 txin.sequence
      h := update h data
    | none => none
  pure (finalize h)

/-- `signature_hash` (`sighash.rs`, lines 37–55): ZIP 143 or 243 before version 5, ZIP 244 in
    version 5, ZIP 229 in version 6. -/
def signatureHash (tx : TransactionData) (signableInput : SignableInput)
    (txidParts : Zip244Digests) : Option Blake2bHash :=
  match tx.version with
  | .sprout _ | .v3 | .v4 => v4SignatureHash tx signableInput
  | .v5 => v5SignatureHash tx signableInput txidParts
  | .v6 => v6SignatureHash tx signableInput txidParts

end ZcashSighash.Verifier.Zakura
