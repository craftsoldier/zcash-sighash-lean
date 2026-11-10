/-
The transcribed `zcash_primitives` on ZIP 244's test vectors, as its own test does
(`src/transaction/tests.rs`, lines 1229–1421, `zip_0244`): each transaction's `to_txid`,
`auth_commitment`, and the signature hash of a shielded input and, under each hash type
`SighashType::parse` accepts, of the vector's transparent input. Where the vector has no
`SIGHASH_SINGLE` digest, the crate still computes one, as its test skips it. Likewise the crates'
own transactions' digests, and `v4_signature_hash` on ZIP 143's and ZIP 243's vectors
(`zip_0143`, `zip_0243`, lines 1084–1148). Then `Transaction::read`: on ZIP 244's vectors and the
crates' own, truncated, and on version headers; on the crate's version 4 transaction, its
identifier and truncations; on ZIP 143's and ZIP 243's, their digests; on versions 1 and 2 and a
version 5 without the overwintered bit; and on the value balance `read_v4` drops.
`Transaction::write` on what it read, and the reader on values at the edges of their range.
Last, Zebra's `sighash` on what the reader reads from ZIP 244's vectors and from the NU7
transactions of `zebra-chain`'s own test, and its `sighash_v4_raw` on ZIP 143's and ZIP 243's
vectors.
-/
import ZcashSighash.Verifier.Zakura
import ZcashSighash.Verifier.Read
import ZcashSighash.Verifier.Zebra
import ZcashSighash.Verifier.Write
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
  match Read.read ctx 0 (bytes ++ rest) with
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

/-- The version 5 transaction's encoding (`zcash_primitives` 0.31.0, `src/transaction/tests.rs`,
    line 124). -/
def v5Encoded : List Byte := hex "050000800a27a726d90a197700000000010000000000000000"

/- As its test checks (lines 155–162): the reader leaves nothing. -/
#guard checkRead ⟨[], []⟩ v5Encoded []
  "328d975581fbf002206ef6f0b69fe57fb47f40ec31c59ac62c3565d4e259e128" none

/-- The first version 6 transaction's encoding (`zcash_primitives` 0.31.0,
    `src/transaction/tests.rs`, line 46), and the trailer its test reads it from (line 52). -/
def v6Encoded : List Byte := hex "0600008098b684d8d90a19770000000001000000000000000000"
def v6Trailer : List Byte := (ascii "next-record" 11).toList

/- As its test checks (lines 89–98): the reader leaves the trailer, and every truncation is an
   error. -/
#guard checkRead ⟨[], []⟩ v6Encoded v6Trailer
  "78296c68a370c2e1f058d997c81c7b011c4562c52fc5ca2994ad59cd179fbe9e" none
#guard (List.range v6Encoded.length).all fun n => (Read.read ⟨[], []⟩ 0 (v6Encoded.take n)).isNone

/-- The second version 6 transaction's encoding (`zakura-primitives` 4.0.0,
    `src/transaction/tests.rs`, line 60). -/
def zakuraV6Encoded : List Byte :=
  hex ("0600008098b684d85b16a5370100000002000000010000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000ffffffff0150c3000000000000015100000000")

/- Read by `zcash_primitives`' reader. -/
#guard checkRead ⟨[], []⟩ zakuraV6Encoded []
  "e11e16887d9aea199fc4eaa3b371c6868ded3e9a2b1c3393a7b0c15f79e73179"
  (some "454423cf6de9acb289a60852144679176cea3bd5e5ec51526d483ced2533e73a")

/-- Whether `TxVersion::read` reads all of `bytes` as a version that `p` accepts. -/
def readsVersion (bytes : List Byte) (p : TxVersion → Bool) : Bool :=
  match Read.readTxVersion bytes with
  | some (v, []) => p v
  | _ => false

/- A header without the overwintered bit is a pre-Overwinter version, whatever its number, which
   `read_v4` reads, as it does versions 3 and 4; with it, the version group ID must be the
   version's own, and version 7 (`nutachyon` only) is unknown; a version of 0 is an error. -/
#guard readsVersion (hex "05000000") fun | .sprout v => v == 5 | _ => false
#guard readsVersion (hex "030000807082c403") fun | .v3 => true | _ => false
#guard readsVersion (hex "0400008085202f89") fun | .v4 => true | _ => false
#guard readsVersion (hex "050000800a27a726") fun | .v5 => true | _ => false
#guard (Read.readTxVersion (hex "0500008098b684d8")).isNone
#guard readsVersion (hex "0600008098b684d8") fun | .v6 => true | _ => false
#guard (Read.readTxVersion (hex "0600008068636174")).isNone
#guard (Read.readTxVersion (hex "0700008068636174")).isNone
#guard (Read.readTxVersion (hex "00000000")).isNone

/-! ## Versions 1 to 4 -/

/-- `zcash_primitives` 0.31.0's `tx_read_write` transaction (`src/transaction/tests/data.rs`,
    lines 1–140): a version 4 transaction of testnet block 280003. -/
def txReadWrite : List Byte := hex
  "0400008085202f89018f642996df1e93a6d79ae5baae3493f423ca6c82e99f3e8d9524fa78bcf16167000000006b\
    483045022100b65e37229707d9cd483940d2ab8bdc0b74b12dda66d02dbdf36fd383b9602a5102204be7fd7a39a4\
    a42dff071a5a2bc51b492d33f0bc394bc87861e1bcaaf2bac93b01210248e78bdc18f1a83110c12e4008b7640269\
    61b168fe8d5a8d947efe6af83cc88effffffff01f0f27018020000001976a914a284d0511d0e520d36f444a36c10\
    bf54b4b017cd88ac00000000d7450400000000000000000000000100ca9a3b0000000000000000000000001331a3\
    059e66aa6ca97a62f56ea234207568566f6971b3722ae0dd82c00399692aacb5fb12ac580ac26624a8cf0a904cd6\
    f4bfea55625205cb58f06b1c197423280deac74eea97598c4314d899a4fd85311e046257d2d4c297f1406cf709d9\
    2a8607f7698d45fe9f41dea3a0571c5da5cfa78e18ebf580c36179d9d6e6320a348f146c407adab4cb310392a5f5\
    b5ab283b78343ba91abc7c4bfe23a3dbaf8037c676e595a26574b1813bc2bf2d2e911f6f3abb0ba6bcac7a2901fb\
    dce65fb07b5636017ef14dff44cdeea730477294f2f8619bd3d5e6be4898bf8d39c0e0eae5a36864625206b9a8f9\
    940bf16650def7926eb0db43b7d7615e4774cf109482f2e807fee6c0c884e8314c67c5d85f4c229cdeab1e964cf0\
    c1adcb47cebfc7c067a0f3c806814a285edbb624f4710629098944ac75e7c9cbc56bd0a029e1110eac60cb4077eb\
    f108fe3e67cd061391e5d6916d5f41c02b8914c12cf605db7d959226e2e8ff71263b9af4c59b0f4db315b74ca2b0\
    b7d25213d5293954c3e51172370fb6c35abe9ce36ef253e3a72e19dac9bd7362c44992974215c82cb90c99488dbd\
    e11963e857cea6b81b8eaae34b7cf5a97d6b60d49fdfa20f5f3c120ef382ca2469604fb0c6842c6d4fae9661665b\
    5cbc612cef132f88fb7da393f356e3ad13fc3557980a7734231453e44079042fb432f55e751484d5d6d30fbc4f99\
    9013d5d4f2fb62f7144e8dcd2ae59546cc4379ad9f1859ef80dec66b1a9b0b7fd2c47bd38302d29c31990329a895\
    876ed1d84db757856e75ce9a1dc7c7472bc218fb8d7c7d028bb02f10efe7fe6a8c9ce034fea66b909c8d4126251c\
    7d6e54f4cfc778cd4f0e0bad1096176f2dd45c45cbe15e118f90ff2545f832f23698f2c9531b52655a4c0c895355\
    9928eedfc756c365cf929b8447dcdc7d823849e02ff68b6278d7542ce0f1070bb1ad913c1a353625f5d35b14cfec\
    84a633d7fe25256dcffe92f9a6f0fe00caaaa5b39cc2ab06768a42a5b40083cea01c96b3e68d0f6a587eaf2da6fd\
    adc82527f186a60471ce98e27d2b11efc47998f3030a7a2e5d0b0a7eb80f6bd0e4b9c8367c6c522d9415f8caec7b\
    0a7318d53dce391cf7e7389c9a74aa6a4c217c288519af81ba2122ca0c5840cc02cf1bcf150cd3df33c0acfd0053\
    e668b926561b924098d97aaab57ee1113df966a422ef9b014617bceef05fb6468e330e2dece3f375e98ef03e5b18\
    a953e2301fccec86200ae432c9c12c30775437f3629714a9fabeb53289402b7fd386cef2b1146723a89d0f81651e\
    00caea2f3ac9eefefb868d85ed2354f530fe38fe3a3a6aab47d42dc21329e3ad1b9d06c0c8d6537456f54ad0453f\
    444175d87ef5cdd1694662e0a1e6e3632ed7a8e76bc7b1b5a418f086d340815ec398f092e97869f5e201c22c8791\
    8f766a3532eb9a4fc9acf196cbc2d0285119a4216d2581cd2d91bcdce868c468f6f34cf49e3a56ce249a2fd8cf36\
    b01b0f77de722bbce267e3e5521688e65222235c91c263d80e28297e929d885b7b9c1a1654b2d0b87577c9a1c725\
    f54415dc5f52dde0695f9f6dcb4b6ee3e3ea702904c11ff92f55534c7ef98ce793d74756a45d4e320a425e982d5b\
    372d6a8d41fb86ba5164816832a481825c8c6ad7270969859e55d2367535060f99857065170466bdb70cb93ab2f9\
    c0e293a0a919843bbf34c2fe61b0c3e32aa7078e83d4c1929e1e1d86141cdeb18920910975db3a7626820599630c\
    423ade233d5d60685524e8d8032b861b4aad2002a8fd17c9282b825f02d353e291379ced00ebaa3c03e01d9c59f4\
    05099d1c3432bad06358d6b1942f0baf710998d10a22d155b0fe849952893126949ff92de3a4c2eeafdf688435e3\
    25d81c2ce008cf6c76030d4d46342ac3372c73986560c4ec35a6f649ef02c11936b7039bc6f5d09438dbe476251b\
    5964b68f02eedff7a9e0ed3e3090965a22f2c552ce3b2b474fd2fc06b50927830a05a303faffd68482d7b7853843\
    2540dd3261ab759b6582129a7f18d801c54319ca52a3c6a3db635044d625e24038ad4277f8d5bf016035165f21b0\
    70e8169d657d6ed1fa7f8ed09b4e1d9ca2e51a24da55e43b3fca9859b2408c26aacbad749ebe882c31e7205e638b\
    b7e2bfc8a3f1c02c0ca7bb9daaab7fcbf845d8002c3de79924dcaadc24bdc0082f4a6b61876f3192a881f59a682d\
    273685d4795c9bd7cccf49de34443a9f9cb35bbf254c50611b7c1324b11094667b6b608c39d1252cebcc4877ceea\
    76e19b842b67f626743fab297776cc9cf79e90e8fce1001790c2e7d5c958647cca5d3397d20afcf29ba44f62a7c6\
    2e908d848d81a79fadbb370aba93b03e41d4bc49e299d6d33faf869f36371414ce646fc2ca6dcff55a6e0639d50c\
    aeb114c418c626b86715436481d1928d55a756a603e7110c3afe963c2b29a478f9d4397b885a67b093a345796219\
    c111b7e94db390aa4bb76b66a534e5e2679b27db5f95fd09a36b05"

/- As its test checks (`src/transaction/tests.rs`, lines 215–226): `Transaction::read` reads all
   of it under Canopy (`0xE9FF75A6`), with the identifier it displays byte-reversed, and `write`
   writes it back. -/
#guard match Read.read ⟨[], []⟩ 0xE9FF75A6 txReadWrite with
  | some (.v4 tx txid, []) =>
    txid.reverse == hex "64f0bd7fe30ce23753358fe3a2dc835b8fba9c0274c4e2c54a6f73114cb55639" &&
    match tx.write ([] : VecU8) with
    | .ok w => w == txReadWrite
    | .error _ => false
  | _ => false

/-- Whether `v4_signature_hash` of what `Transaction::read` reads from the vector, under its branch
    ID, is the vector's digest, as `zip_0143` and `zip_0243` read and hash it (lines 1085–1148),
    and whether `write` writes back what was read. -/
def checkReadV4 (v : LegacyVector) : Bool :=
  match Read.read ⟨[], []⟩ (.ofNat _ v.branch.id) (hex v.tx) with
  | some (.v4 tx _, []) =>
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
    (match input?, zip143Digests tx with
      | some input, some digests => v4SignatureHash tx input digests == some (hex v.sighash)
      | _, _ => false) &&
    match tx.write ([] : VecU8) with
    | .ok w => w == hex v.tx
    | .error _ => false
  | _ => false

#guard (zip143Vectors ++ zip243Vectors).map checkReadV4 = List.replicate 20 true

/-- Whether `Transaction::read` reads all of `bytes` as a transaction of version 1 to 4, and
    `write` writes `bytes` back. -/
def checkV4RoundTrip (bytes : List Byte) : Bool :=
  match Read.read ⟨[], []⟩ 0 bytes with
  | some (.v4 tx _, []) =>
    match tx.write ([] : VecU8) with
    | .ok w => w == bytes
    | .error _ => false
  | _ => false

/- A version 1 transaction, which has no JoinSplits, a version 2 one with one JoinSplit and its
   BCTV14 proof, and a version 5 one without the overwintered bit, which `read` hands to
   `read_v4` as version 2's kind, zero bytes but for the header and the counts. -/
#guard checkV4RoundTrip (hex "01000000" ++ hex "0000" ++ hex "00000000")
#guard checkV4RoundTrip (hex "02000000" ++ hex "0000" ++ hex "00000000" ++ hex "01" ++
  List.replicate 1802 0 ++ List.replicate 96 0)
#guard checkV4RoundTrip (hex "05000000" ++ hex "0000" ++ hex "00000000" ++ hex "00")

/- `Transaction::read` rejects every truncation of the crate's version 4 transaction. -/
#guard (List.range txReadWrite.length).all fun n =>
  (Read.read ⟨[], []⟩ 0xE9FF75A6 (txReadWrite.take n)).isNone

/-- A version 4 transaction with no Sapling Spend or Output and a value balance of 1. -/
def droppedValueBalance : List Byte :=
  hex "0400008085202f89" ++ hex "0000" ++ hex "0000000000000000" ++ toLeBytes 8 (1 : BitVec 64) ++
    hex "000000"

/- With no Sapling Spend or Output, `read_v4` reads the value balance and drops it, and `write`
   writes zero in its place: the bytes written back are not the ones read. -/
#guard match Read.read ⟨[], []⟩ 0 droppedValueBalance with
  | some (.v4 tx _, []) =>
    match tx.write ([] : VecU8) with
    | .ok w => w == hex "0400008085202f89" ++ hex "0000" ++ hex "0000000000000000" ++
        toLeBytes 8 (0 : BitVec 64) ++ hex "000000"
    | .error _ => false
  | _ => false

/-! ## `Transaction::write` -/

/-- Whether `Transaction::write` writes back exactly the bytes `Transaction::read` read. -/
def checkWrite (bytes : List Byte) : Bool :=
  match Read.read ⟨[], []⟩ 0 bytes with
  | some (.tx tx, []) =>
    match tx.write ([] : VecU8) with
    | .ok w => w == bytes
    | .error _ => false
  | _ => false

#guard zip244Vectors.all fun v => checkWrite (hex v.tx)

/- The crates' own: `zcash_primitives` 0.31.0's `tx_bytes(&tx) == encoded` (`src/transaction/
   tests.rs`, lines 86 and 153), and `zakura-primitives` 4.0.0's version 6 transaction. -/
#guard checkWrite v5Encoded
#guard checkWrite v6Encoded
#guard checkWrite zakuraV6Encoded

/-- A version 6 transaction under consensus branch ID `branchId`, with one Action in its Ironwood
    bundle if `ironwood`, or in its Orchard bundle otherwise, zero bytes but for its header. -/
def withV6Action (branchId : BitVec 32) (ironwood : Bool) : List Byte :=
  let bundle := hex "01" ++ List.replicate 820 0 ++ List.replicate 42 0 ++ List.replicate 128 0
  hex "0600008098b684d8" ++ toLeBytes 4 branchId ++ hex "0000000001000000" ++ hex "00000000" ++
    if ironwood then hex "00" ++ bundle else bundle ++ hex "00"

/-- What `Transaction::write` writes of what `Transaction::read` read from `withV6Action`:
    whether its bytes are the ones read, or none for a write error. -/
def writesV6Action (branchId : BitVec 32) (ironwood : Bool) : Option (Option Bool) :=
  match Read.read ⟨[], []⟩ 0 (withV6Action branchId ironwood) with
  | some (.tx tx, []) =>
    match tx.write ([] : VecU8) with
    | .ok w => some (some (w == withV6Action branchId ironwood))
    | .error _ => some none
  | _ => none

/- `write_v6_bundle` writes back an Orchard bundle read under NU6.3 (`0x37A5165B`) or NU7
   (`0x77190AD9`), whose bundle version is `orchard_v3`, and rejects one read under NU5, NU6 or
   NU6.1 (`orchard_insecure_v1`) or NU6.2 (`orchard_v2`), as Zebra does when it parses them. An
   Ironwood bundle, `ironwood_v3` from NU6.3 on, is written back, and has no version before. A
   bundle with no version, as under Canopy, the crate's `read_bundle` already rejects
   (`components/orchard.rs`, lines 114–120), as it would every fixture here for its zero-byte
   points; these test the transcription. -/
#guard writesV6Action 0x37A5165B false == some (some true)
#guard writesV6Action 0x77190AD9 false == some (some true)
#guard writesV6Action 0xC2D6D0B4 false == some none
#guard writesV6Action 0xC8E71055 false == some none
#guard writesV6Action 0x4DEC4DF0 false == some none
#guard writesV6Action 0x5437F330 false == some none
#guard writesV6Action 0xE9FF75A6 false == some none
#guard writesV6Action 0x37A5165B true == some (some true)
#guard writesV6Action 0x77190AD9 true == some (some true)
#guard writesV6Action 0x5437F330 true == some none
#guard writesV6Action 0xC2D6D0B4 true == some none

/-! ## Values -/

/-- A version 5 transaction with one Sapling Output, zero bytes but for its header and its value
    balance `vb`. -/
def withValueBalance (vb : BitVec 64) : List Byte :=
  hex "050000800a27a726d90a19770000000001000000" ++ hex "00000001" ++ List.replicate 756 0 ++
    toLeBytes 8 vb ++ List.replicate 256 0 ++ hex "00"

/-- Whether `Transaction::read` reads all of `withValueBalance vb`, into a transaction whose
    Sapling value balance is `vb`. -/
def readsValueBalance (vb : BitVec 64) : Bool :=
  match Read.read ⟨[], []⟩ 0 (withValueBalance vb) with
  | some (.tx tx, []) => (tx.saplingBundle.map (·.valueBalance)) == some vb
  | _ => false

/- `read_amount`, called for a Sapling value balance by `read_v5_bundle` (`components/sapling.rs`,
   line 458), accepts one in `-MAX_MONEY..=MAX_MONEY`, -1 included, and rejects one outside it,
   `i64::MIN` included (`zcash_protocol` 0.11.0, `src/value.rs`, lines 58–66). These test the
   transcription, which leaves out the point checks the Rust would fail these zero bytes on. -/
#guard readsValueBalance (.ofInt 64 2100000000000000)
#guard readsValueBalance (.ofInt 64 (-2100000000000000))
#guard readsValueBalance (.ofInt 64 (-1))
#guard (Read.read ⟨[], []⟩ 0 (withValueBalance (.ofInt 64 2100000000000001))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withValueBalance (.ofInt 64 (-2100000000000001)))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withValueBalance (.ofNat 64 (2 ^ 63)))).isNone

/-- A version 5 transaction with one Orchard Action, zero bytes but for its header and its value
    balance `vb`. -/
def withOrchardValueBalance (vb : BitVec 64) : List Byte :=
  hex "050000800a27a726d90a19770000000001000000" ++ hex "0000000001" ++ List.replicate 820 0 ++
    hex "00" ++ toLeBytes 8 vb ++ List.replicate 32 0 ++ hex "00" ++ List.replicate 128 0

/-- Whether `Transaction::read` reads all of `withOrchardValueBalance vb`, into a transaction whose
    Orchard value balance is `vb`. -/
def readsOrchardValueBalance (vb : BitVec 64) : Bool :=
  match Read.read ⟨[], []⟩ 0 (withOrchardValueBalance vb) with
  | some (.tx tx, []) => (tx.orchardBundle.map (·.valueBalance)) == some vb
  | _ => false

/- The same of an Orchard value balance (`read_bundle`, `components/orchard.rs`, line 122). The
   Rust would reject this bundle for its empty proof (`try_from_parts`, lines 139–152), a check
   the transcription leaves out. -/
#guard readsOrchardValueBalance (.ofInt 64 2100000000000000)
#guard readsOrchardValueBalance (.ofInt 64 (-2100000000000000))
#guard readsOrchardValueBalance (.ofInt 64 (-1))
#guard (Read.read ⟨[], []⟩ 0 (withOrchardValueBalance (.ofInt 64 2100000000000001))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withOrchardValueBalance (.ofInt 64 (-2100000000000001)))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withOrchardValueBalance (.ofNat 64 (2 ^ 63)))).isNone

/-- A version 6 transaction with one Ironwood Action, zero bytes but for its header and its value
    balance `vb`. -/
def withIronwoodValueBalance (vb : BitVec 64) : List Byte :=
  hex "0600008098b684d8d90a19770000000001000000" ++ hex "000000000001" ++ List.replicate 820 0 ++
    hex "00" ++ toLeBytes 8 vb ++ List.replicate 32 0 ++ hex "00" ++ List.replicate 128 0

/-- Whether `Transaction::read` reads all of `withIronwoodValueBalance vb`, into a transaction whose
    Ironwood value balance is `vb`. -/
def readsIronwoodValueBalance (vb : BitVec 64) : Bool :=
  match Read.read ⟨[], []⟩ 0 (withIronwoodValueBalance vb) with
  | some (.tx tx, []) => (tx.ironwoodBundle.map (·.valueBalance)) == some vb
  | _ => false

/- The same of an Ironwood value balance. -/
#guard readsIronwoodValueBalance (.ofInt 64 2100000000000000)
#guard readsIronwoodValueBalance (.ofInt 64 (-2100000000000000))
#guard (Read.read ⟨[], []⟩ 0 (withIronwoodValueBalance (.ofInt 64 2100000000000001))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withIronwoodValueBalance (.ofInt 64 (-2100000000000001)))).isNone

/-- A version 5 transaction with one transparent output of value `v`, and nothing else. -/
def withOutputValue (v : BitVec 64) : List Byte :=
  hex "050000800a27a726d90a19770000000001000000" ++ hex "0001" ++ toLeBytes 8 v ++
    hex "00000000"

/-- Whether `Transaction::read` reads all of `withOutputValue v`, into a transaction whose output
    has value `v`. -/
def readsOutputValue (v : BitVec 64) : Bool :=
  match Read.read ⟨[], []⟩ 0 (withOutputValue v) with
  | some (.tx tx, []) => (tx.transparentBundle.map (·.vout.map (·.value))) == some [v]
  | _ => false

/- An output's value is at most `MAX_MONEY` (`TxOut::read`, `zcash_transparent` 0.11.0,
   `src/bundle.rs`, lines 385–398). The Rust reads it as a signed `i64` and rejects a negative
   one; the transcription reads it as unsigned, which accepts the same values. -/
#guard readsOutputValue (.ofNat 64 2100000000000000)
#guard readsOutputValue 0
#guard (Read.read ⟨[], []⟩ 0 (withOutputValue (.ofNat 64 2100000000000001))).isNone
#guard (Read.read ⟨[], []⟩ 0 (withOutputValue (.ofInt 64 (-1)))).isNone

/-! ## Zebra -/

/-- A coin as Zebra holds it, if its value is in range. -/
def zebraOutput (value : ℕ) (script : List Byte) : Option Zebra.Output :=
  if h : value ≤ Native.MAX_MONEY then
    some ⟨BitVec.ofNat 64 value, ⟨script⟩, (BitVec.toNat_ofNat _ _ ▸ Nat.mod_le _ _).trans h⟩
  else none

/-- Whether Zebra's digests of the vector's transaction are the vector's: its shielded signature
    digest, and its transparent input's under each hash type. The transaction is the one
    `Transaction::read` reads, under its own consensus branch ID, spending the vector's coins
    (none for a coinbase, as Zebra looks up none). Where the vector has no `SIGHASH_SINGLE`
    digest, Zebra still computes one. -/
def checkZebra (v : Zip244Vector) : Bool :=
  match (v.amounts.zip v.scriptPubKeys).mapM (fun (a, s) => zebraOutput a (hex s)),
    Read.read ⟨[], []⟩ 0 (hex v.tx) with
  | some outs, some (.tx tx, []) =>
    let coinbase := (tx.transparentBundle.map fun b : Transparent.Bundle => b.isCoinbase).getD false
    let outs := if coinbase then [] else outs
    match Zebra.PrecomputedTxData.new tx (some tx.consensusBranchId) outs with
    | some (.ok data) =>
      Zebra.sighash data 0x01 none == some (hex v.sighashShielded) &&
      match v.transparentInput with
      | none => true
      | some i => (hashTypes v).all fun (ht, expected) =>
        let digest := Zebra.sighash data (ht.toByte.setWidth 32) (some (i, []))
        match expected with
        | some e => digest == some (hex e)
        | none => digest.isSome
    | _ => false
  | _, _ => false

#guard zip244Vectors.map checkZebra = List.replicate 10 true

/-- Whether Zebra's `sighash_v4_raw`, with the vector's raw hash type, gives the vector's digest.
    The transaction holds branch ID 0 and is rebuilt under the vector's, so the digest is right
    only if the rebuild's branch ID is the one hashed. Every input spends a coin with the
    vector's amount and its script code as the lock script. For a shielded vector, `sighash` with
    `HashType::ALL`, as Zebra computes it, must give the digest too. -/
def checkZebraV4 (v : LegacyVector) : Bool :=
  match (legacyDecoder (.ofNat _ v.branch.id) []).run' (hex v.tx),
    zebraOutput v.amount (hex v.scriptCode) with
  | some stx, some coin =>
    let tx := { legacyToTransactionData stx (match stx.format with | .v3 => false | .v4 => true)
      with consensusBranchId := 0 }
    let outs := List.replicate stx.transparent.vin.length coin
    match Zebra.PrecomputedTxData.new tx (some (.ofNat _ v.branch.id)) outs with
    | some (.ok data) =>
      Zebra.sighashV4Raw data (.ofNat _ v.hashType) (v.transparentInput.map (·, hex v.scriptCode))
        == some (hex v.sighash) &&
      (v.transparentInput.isSome || Zebra.sighash data 0x01 none == some (hex v.sighash))
    | _ => false
  | _, _ => false

#guard (zip143Vectors ++ zip243Vectors).map checkZebraV4 = List.replicate 20 true

/-- Whether Zebra gives the NU7 transaction `bytes` the shielded signature digest `digest` under
    NU7 (branch ID `0x77190AD9`), and rejects it under NU6.3 (`0x37A5165B`; `zebra-chain`
    15.0.0, `src/parameters/network_upgrade.rs`, lines 243 and 245). -/
def checkZebraNu7 (bytes : List Byte) (digest : String) : Bool :=
  match Read.read ⟨[], []⟩ 0 bytes with
  | some (.tx tx, []) =>
    (match Zebra.PrecomputedTxData.new tx (some 0x77190AD9) [] with
      | some (.ok data) => Zebra.sighash data 0x01 none == some (hex digest)
      | _ => false) &&
    match Zebra.PrecomputedTxData.new tx (some 0x37A5165B) [] with
    | some (.error .invalidConsensusBranchId) => true
    | _ => false
  | _ => false

/- `zebra-chain` 15.0.0's `nu7_branch_id_and_transaction_formats` (`src/parameters/tests.rs`,
   lines 175–239), on both NU7 transactions. -/
#guard checkZebraNu7 v5Encoded "328d975581fbf002206ef6f0b69fe57fb47f40ec31c59ac62c3565d4e259e128"
#guard checkZebraNu7 v6Encoded "78296c68a370c2e1f058d997c81c7b011c4562c52fc5ca2994ad59cd179fbe9e"

end ZcashSighash.Tests
