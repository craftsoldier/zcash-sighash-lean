/-
The transcribed `zcash_primitives` on ZIP 244's test vectors, as its own test does
(`src/transaction/tests.rs`, lines 1229–1421, `zip_0244`): each transaction's `to_txid`,
`auth_commitment`, and the signature hash of a shielded input and, under each hash type
`SighashType::parse` accepts, of the vector's transparent input. Where the vector has no
`SIGHASH_SINGLE` digest, the crate still computes one, as its test skips it. Likewise the crates'
own transactions' digests, and `v4_signature_hash` on ZIP 143's and ZIP 243's vectors
(`zip_0143`, `zip_0243`, lines 1084–1148).
-/
import ZcashSighash.Verifier.Zakura
import ZcashSighash.Verifier.Read
import ZcashSighash.Tests.Spec

namespace ZcashSighash.Tests

open ZcashSighash.Spec
open ZcashSighash.Verifier

/-- A decoded transaction as `Transaction::read` holds it: a bundle only when it is not empty,
    each Sapling spend with the shared anchor, the Orchard bundle in the Orchard pool, no Ironwood
    bundle (the crates' version 6 transactions have none), and the spent coins as the authorizing
    context, as the crate's test builds it. -/
def toTransactionData (tx : Spec.Transaction) : TransactionData where
  version := match tx.format with | .v5 => .v5 | .v6 _ => .v6
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

/-- Whether the transcription gives the crate vector's digests. -/
def checkVerifierCrate (v : CrateVector) : Bool :=
  let tx := toTransactionData v.tx
  match tx.txIdDigests, PrecomputedSighashData.newZip244 tx with
  | some digests, some (some precomputed) =>
    (v.headerDigest.all fun d => digests.headerDigest == hex d) &&
    toTxid tx.version tx.consensusBranchId digests == some (some (hex v.txid)) &&
    (v.authDigest.all fun d => tx.authCommitment == some (hex d)) &&
    v.sighashShielded.all fun d => precomputed.signatureHash .shielded == some (hex d)
  | _, _ => false

#guard crateVectors.map checkVerifierCrate = List.replicate 3 true

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

/-- Whether Zakura gives the crate vector's digests. -/
def checkZakuraCrate (v : CrateVector) : Bool :=
  let tx := toTransactionData v.tx
  match Zakura.TransactionData.txIdDigests tx with
  | some digests =>
    (v.headerDigest.all fun d => digests.headerDigest == hex d) &&
    Zakura.toTxid tx.version tx.consensusBranchId digests == some (hex v.txid) &&
    (v.authDigest.all fun d => Zakura.TransactionData.authCommitment tx == some (hex d)) &&
    v.sighashShielded.all fun d => Zakura.signatureHash tx .shielded digests == some (hex d)
  | none => false

#guard crateVectors.map checkZakuraCrate = List.replicate 3 true

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

/-! ## `Transaction::read` -/

/-- Whether `Transaction::read` reads `bytes` into a transaction with identifier `txid` and auth
    digest `authDigest`, leaving `rest`. -/
def checkRead (ctx : Transparent.AuthorizingContext) (bytes rest : List Byte) (txid : String)
    (authDigest : Option String) : Bool :=
  match Read.read ctx (bytes ++ rest) with
  | some (.tx tx, rest') =>
    rest' == rest &&
    match tx.txIdDigests with
    | some digests =>
      toTxid tx.version tx.consensusBranchId digests == some (some (hex txid)) &&
      authDigest.all fun d => tx.authCommitment == some (hex d)
    | none => false
  | _ => false

#guard zip244Vectors.map (fun v => checkRead
  ⟨v.amounts.map (BitVec.ofNat 64), v.scriptPubKeys.map fun s => ⟨hex s⟩⟩ (hex v.tx) []
  v.txid (some v.authDigest)) = List.replicate 10 true

/- The version 5 transaction's encoding (`zcash_primitives` 0.31.0, `src/transaction/tests.rs`,
   line 124): as its test checks (lines 155–162), the reader leaves nothing. -/
#guard checkRead ⟨[], []⟩ (hex "050000800a27a726d90a197700000000010000000000000000") []
  "328d975581fbf002206ef6f0b69fe57fb47f40ec31c59ac62c3565d4e259e128" none

/-- The first version 6 transaction's encoding (`zcash_primitives` 0.31.0,
    `src/transaction/tests.rs`, line 46), and the trailer its test reads it from (line 52). -/
def v6Encoded : List Byte := hex "0600008098b684d8d90a19770000000001000000000000000000"
def v6Trailer : List Byte := (ascii "next-record" 11).toList

/- As its test checks (lines 89–98): the reader leaves the trailer, and every truncation is an
   error. -/
#guard checkRead ⟨[], []⟩ v6Encoded v6Trailer
  "78296c68a370c2e1f058d997c81c7b011c4562c52fc5ca2994ad59cd179fbe9e" none
#guard (List.range v6Encoded.length).all fun n => (Read.read ⟨[], []⟩ (v6Encoded.take n)).isNone

/- The second version 6 transaction's encoding (`zakura-primitives` 4.0.0,
   `src/transaction/tests.rs`, line 60), read by `zcash_primitives`' reader. -/
#guard checkRead ⟨[], []⟩
  (hex ("0600008098b684d85b16a5370100000002000000010000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000ffffffff0150c3000000000000015100000000"))
  []
  "e11e16887d9aea199fc4eaa3b371c6868ded3e9a2b1c3393a7b0c15f79e73179"
  (some "454423cf6de9acb289a60852144679176cea3bd5e5ec51526d483ced2533e73a")

/-- Whether `Transaction::read` hands `bytes` to `read_v4`, with a version that `p` accepts. -/
def readsV4 (bytes : List Byte) (p : TxVersion → Bool) : Bool :=
  match Read.read ⟨[], []⟩ bytes with
  | some (.readV4 v, _) => p v
  | _ => false

/-- Whether `TxVersion::read` reads all of `bytes` as a version that `p` accepts. -/
def readsVersion (bytes : List Byte) (p : TxVersion → Bool) : Bool :=
  match Read.readTxVersion bytes with
  | some (v, []) => p v
  | _ => false

/- A header without the overwintered bit is a pre-Overwinter version, whatever its number, and
   goes to `read_v4`, as versions 3 and 4 do; with it, the version group ID must be the version's
   own, and version 7 (`nutachyon` only) is unknown; a version of 0 is an error. -/
#guard readsV4 (hex "05000000") fun | .sprout v => v == 5 | _ => false
#guard readsV4 (hex "030000807082c403") fun | .v3 => true | _ => false
#guard readsV4 (hex "0400008085202f89") fun | .v4 => true | _ => false
#guard readsVersion (hex "050000800a27a726") fun | .v5 => true | _ => false
#guard (Read.readTxVersion (hex "0500008098b684d8")).isNone
#guard readsVersion (hex "0600008098b684d8") fun | .v6 => true | _ => false
#guard (Read.readTxVersion (hex "0600008068636174")).isNone
#guard (Read.readTxVersion (hex "0700008068636174")).isNone
#guard (Read.readTxVersion (hex "00000000")).isNone

end ZcashSighash.Tests
