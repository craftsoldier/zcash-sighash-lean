/-
The transcribed `zcash_primitives` on ZIP 244's test vectors, as its own test does
(`src/transaction/tests.rs`, lines 1229–1421, `zip_0244`): each transaction's `to_txid`,
`auth_commitment`, and the signature hash of a shielded input and, under each hash type
`SighashType::parse` accepts, of the vector's transparent input. Where the vector has no
`SIGHASH_SINGLE` digest, the crate still computes one, as its test skips it. Likewise the two
version 6 transactions' digests, and `v4_signature_hash` on ZIP 143's and ZIP 243's vectors
(`zip_0143`, `zip_0243`, lines 1084–1148).
-/
import ZcashSighash.Verifier.Zakura
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
  sproutBundle := none
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

/-- A decoded version 3 or 4 transaction as `Transaction::read` holds it. -/
def legacyToTransactionData (tx : Spec.LegacyTransaction) (v4 : Bool) : TransactionData where
  version := if v4 then .v4 else .v3
  consensusBranchId := tx.header.consensusBranchId
  lockTime := tx.header.lockTime
  expiryHeight := tx.header.expiryHeight
  sproutBundle := if tx.joinSplits = [] then none else some
    { joinsplits := tx.joinSplits.map fun js =>
        { vpubOld := js.vpubOld, vpubNew := js.vpubNew, anchor := js.anchor
          nullifiers := js.nullifiers, commitments := js.commitments
          ephemeralKey := js.ephemeralKey, randomSeed := js.randomSeed, macs := js.macs
          proof := if h : js.zkproof.length = 192 then .groth ⟨js.zkproof, h⟩
            else .phgr ⟨js.zkproof.take 296 ++ List.replicate (296 - js.zkproof.length) 0,
              by simp; omega⟩
          ciphertexts := js.encCiphertexts }
      joinsplitPubkey := tx.joinSplitPubKey, joinsplitSig := List.Vector.replicate 64 0 }
  transparentBundle :=
    if tx.transparent.vin = [] ∧ tx.transparent.vout = [] then none
    else some
      { vin := tx.transparent.vin.map fun i => ⟨⟨i.prevout.hash, i.prevout.n⟩, ⟨[]⟩, i.nSequence⟩
        vout := tx.transparent.vout.map fun o => ⟨o.value, ⟨o.scriptPubKey⟩⟩
        authorization := ⟨[], []⟩ }
  saplingBundle :=
    if tx.saplingSpends = [] ∧ tx.saplingOutputs = [] then none
    else some
      { shieldedSpends := tx.saplingSpends.map fun s =>
          ⟨s.cv, s.anchor, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩
        shieldedOutputs := tx.saplingOutputs.map fun o =>
          ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, o.zkproof⟩
        valueBalance := tx.valueBalance
        bindingSig := List.Vector.replicate 64 0 }
  orchardBundle := none
  ironwoodBundle := none

/-- Whether `v4_signature_hash` gives the vector's signature digest. -/
def checkLegacyVerifier (v : LegacyVector) : Bool :=
  match (legacyDecoder (.ofNat _ v.branch.id) []).run' (hex v.tx) with
  | none => false
  | some stx =>
    let tx := legacyToTransactionData stx (match stx.format with | .v3 => false | .v4 => true)
    let input? : Option SignableInput := match v.transparentInput, tx.transparentBundle with
      | none, _ => some .shielded
      | some i, some bundle =>
        match Transparent.SighashType.parse (.ofNat _ v.hashType) with
        | none => none
        | some hashType =>
          match Transparent.SignableInput.fromParts bundle hashType i ⟨hex v.scriptCode⟩
              ⟨hex v.scriptCode⟩ (.ofNat _ v.amount) with
          | .ok input => some (.transparent input)
          | .error _ => none
      | some _, none => none
    match input?, zip143Digests tx with
    | some input, some digests => v4SignatureHash tx input digests == some (hex v.sighash)
    | _, _ => false

#guard zip143Vectors.map checkLegacyVerifier = List.replicate 10 true

#guard zip243Vectors.map checkLegacyVerifier = List.replicate 10 true

/-! ## Zakura -/

/-- Whether Zakura's digests are the vector's (`zakura-primitives` 4.0.0's own `zip_0244` test). -/
def checkZakura (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some stx =>
    let tx := toTransactionData stx
    match Zakura.TransactionData.txIdDigests tx with
    | some digests =>
      Zakura.toTxid tx.version tx.consensusBranchId digests == some (hex v.txid) &&
      Zakura.TransactionData.authCommitment tx == some (hex v.authDigest) &&
      Zakura.signatureHash tx .shielded digests == some (hex v.sighashShielded) &&
      match v.transparentInput, tx.transparentBundle with
      | none, _ => true
      | some i, some bundle =>
        (hashTypes v).all fun (ht, expected) =>
          match Transparent.SighashType.parse ht.toByte with
          | none => false
          | some hashType =>
            match Transparent.SignableInput.fromParts bundle hashType i
                (bundle.authorization.inputScriptpubkeys.getD i ⟨[]⟩)
                (bundle.authorization.inputScriptpubkeys.getD i ⟨[]⟩)
                (bundle.authorization.inputAmounts.getD i 0) with
            | .error _ => false
            | .ok input =>
              let digest := Zakura.signatureHash tx (.transparent input) digests
              match expected with
              | some e => digest == some (hex e)
              | none => digest.isSome
      | some _, none => false
    | none => false

#guard zip244Vectors.map checkZakura = List.replicate 10 true

/-- Whether Zakura gives the version 6 vector's digests. -/
def checkZakuraV6 (v : V6Vector) : Bool :=
  let tx := toTransactionDataV6 v.tx
  match Zakura.TransactionData.txIdDigests tx with
  | some digests =>
    digests.headerDigest == hex v.headerDigest &&
    Zakura.toTxid tx.version tx.consensusBranchId digests == some (hex v.txid) &&
    (v.authDigest.all fun d => Zakura.TransactionData.authCommitment tx == some (hex d)) &&
    v.sighashShielded.all fun d => Zakura.signatureHash tx .shielded digests == some (hex d)
  | none => false

#guard v6Vectors.map checkZakuraV6 = [true, true]

/-- Whether Zakura's `v4_signature_hash` gives the vector's digest. -/
def checkZakuraLegacy (v : LegacyVector) : Bool :=
  match (legacyDecoder (.ofNat _ v.branch.id) []).run' (hex v.tx) with
  | none => false
  | some stx =>
    let tx := legacyToTransactionData stx (match stx.format with | .v3 => false | .v4 => true)
    let input? : Option SignableInput := match v.transparentInput, tx.transparentBundle with
      | none, _ => some .shielded
      | some i, some bundle =>
        match Transparent.SighashType.parse (.ofNat _ v.hashType) with
        | none => none
        | some hashType =>
          match Transparent.SignableInput.fromParts bundle hashType i ⟨hex v.scriptCode⟩
              ⟨hex v.scriptCode⟩ (.ofNat _ v.amount) with
          | .ok input => some (.transparent input)
          | .error _ => none
      | some _, none => none
    match input? with
    | some input => Zakura.v4SignatureHash tx input == some (hex v.sighash)
    | none => false

#guard (zip143Vectors ++ zip243Vectors).map checkZakuraLegacy = List.replicate 20 true

end ZcashSighash.Tests
