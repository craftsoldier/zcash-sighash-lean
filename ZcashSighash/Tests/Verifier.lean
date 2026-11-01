/-
The transcribed `zcash_primitives` on ZIP 244's test vectors, as its own test does
(`src/transaction/tests.rs`, lines 1229–1421, `zip_0244`): each transaction's `to_txid`,
`auth_commitment`, and the signature hash of a shielded input and, under each hash type
`SighashType::parse` accepts, of the vector's transparent input. Where the vector has no
`SIGHASH_SINGLE` digest, the crate still computes one, as its test skips it. Likewise the two
version 6 transactions' digests.
-/
import ZcashSighash.Verifier.Sighash
import ZcashSighash.Tests.Spec

namespace ZcashSighash.Tests

open ZcashSighash.Spec
open ZcashSighash.Verifier

/-- A decoded version 5 transaction as `Transaction::read` holds it: a bundle only when it is
    not empty, each Sapling spend with the shared anchor, the Orchard bundle in the Orchard pool,
    and the spent coins as the authorizing context, as the crate's test builds it. -/
def toTransactionData (tx : Spec.Transaction) : TransactionData where
  version := .v5
  consensusBranchId := tx.header.consensusBranchId
  lockTime := tx.header.lockTime
  expiryHeight := tx.header.expiryHeight
  transparentBundle :=
    if tx.transparent.vin = [] ∧ tx.transparent.vout = [] then none
    else some
      { vin := (tx.transparent.vin.zip tx.scriptSigs).map fun (i, s) =>
          ⟨⟨i.prevout.hash, i.prevout.n⟩, ⟨s⟩, i.nSequence⟩
        vout := tx.transparent.vout.map fun o => ⟨o.value, ⟨o.scriptPubKey⟩⟩
        authorization := ⟨tx.transparent.vin.map (·.spent.value),
          tx.transparent.vin.map fun i => ⟨i.spent.scriptPubKey⟩⟩ }
  saplingBundle :=
    if tx.sapling.spends = [] ∧ tx.sapling.outputs = [] then none
    else some
      { shieldedSpends := tx.sapling.spends.map fun s =>
          ⟨s.cv, tx.sapling.anchor, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩
        shieldedOutputs := tx.sapling.outputs.map fun o =>
          ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, o.zkproof⟩
        valueBalance := tx.sapling.valueBalance
        bindingSig := tx.sapling.bindingSig }
  orchardBundle :=
    let action (a : Spec.Action) : Orchard.Action :=
      ⟨a.nullifier, a.rk, a.cmx, a.ephemeralKey, a.encCiphertext, a.outCiphertext, a.cv,
        a.spendAuthSig⟩
    match tx.orchard.actions with
    | [] => none
    | a :: as => some
      { actions := ⟨action a, as.map action⟩, flagByte := tx.orchard.flags
        valueBalance := tx.orchard.valueBalance, anchor := tx.orchard.anchor
        proof := tx.orchard.proofs, bindingSignature := tx.orchard.bindingSig
        valuePool := .orchard }
  ironwoodBundle := none

/-- Whether the transcription gives the vector's digests. -/
def checkVerifier (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some stx =>
    let tx := toTransactionData stx
    match tx.txIdDigests, PrecomputedSighashData.newZip244 tx with
    | some digests, some (some precomputed) =>
      toTxid tx.version tx.consensusBranchId digests == some (some (hex v.txid)) &&
      tx.authCommitment == some (hex v.authDigest) &&
      precomputed.signatureHash .shielded == some (hex v.sighashShielded) &&
      match v.transparentInput, tx.transparentBundle with
      | none, _ => true
      | some i, some bundle =>
        (hashTypes v).all fun (ht, expected) =>
          match Transparent.SighashType.parse ht.toByte with
          | none => false
          | some hashType =>
            match Transparent.SignableInput.fromParts bundle hashType i
                (bundle.authorization.inputScriptpubkeys.getD i ⟨[]⟩)
                (bundle.authorization.inputAmounts.getD i 0) with
            | .error _ => false
            | .ok input =>
              let digest := precomputed.signatureHash (.transparent input)
              match expected with
              | some e => digest == some (hex e)
              | none => digest.isSome
      | some _, none => false
    | _, _ => false

#guard zip244Vectors.map checkVerifier = List.replicate 10 true

/-- A version 6 vector's transaction, as `TransactionData::from_parts_v6` builds it. -/
def toTransactionDataV6 (tx : Spec.Transaction) : TransactionData :=
  { toTransactionData tx with version := .v6 }

/-- Whether the transcription gives the version 6 vector's digests. -/
def checkVerifierV6 (v : V6Vector) : Bool :=
  let tx := toTransactionDataV6 v.tx
  match tx.txIdDigests, PrecomputedSighashData.newZip244 tx with
  | some digests, some (some precomputed) =>
    digests.headerDigest == hex v.headerDigest &&
    toTxid tx.version tx.consensusBranchId digests == some (some (hex v.txid)) &&
    (v.authDigest.all fun d => tx.authCommitment == some (hex d)) &&
    v.sighashShielded.all fun d => precomputed.signatureHash .shielded == some (hex d)
  | _, _ => false

#guard v6Vectors.map checkVerifierV6 = [true, true]

end ZcashSighash.Tests
