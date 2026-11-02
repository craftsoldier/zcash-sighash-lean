/-
Zakura's own ZIP 244 / ZIP 229 digests on ZIP 244's test vectors and the two version 6
transactions: each transaction's identifier and auth digest, its shielded signature digest, and
its transparent input's signature digest under each hash type the vector gives one for. Its own
ZIP 243 digest on ZIP 243's vectors. Then the signature check's failure cases: every byte a
signature can end with, through Zakura's callback over its own `SigHasher`. Last, the crate's
own tests of the block's auth data root.
-/
import ZcashSighash.Verifier.NativeV4
import ZcashSighash.Verifier.BlockCommitment
import ZcashSighash.Proofs.Native
import ZcashSighash.Verifier.Parse
import ZcashSighash.Tests.Spec

namespace ZcashSighash.Tests

open ZcashSighash.Spec
open ZcashSighash.Verifier
open ZcashSighash.Verifier.Native (Parts CoinbaseScript Zip244SighashCache)

/-- A coinbase input's `scriptSig`, if the transaction has one: a test vector's coinbase
    `scriptSig` need not encode a height, so the test rebuilds it whole. -/
def coinbaseScriptSig (tx : Spec.Transaction) : List Byte :=
  match (tx.transparent.vin.zip tx.scriptSigs).find? (·.1.prevout.IsNull) with
  | some (_, s) => s
  | none => []

/-- `push_num` that rebuilds the transaction's coinbase `scriptSig`, with empty data. -/
def coinbaseScriptOf (tx : Spec.Transaction) : CoinbaseScript :=
  ⟨fun _ => coinbaseScriptSig tx, []⟩

/-- A decoded transaction as Zakura's parser holds it: a null prevout as a coinbase input, each
    component only when it is not empty. -/
def toParts (tx : Spec.Transaction) : Parts where
  version := match tx.format with | .v5 => .v5 | .v6 _ => .v6
  consensusBranchId := tx.header.consensusBranchId
  lockTime := tx.header.lockTime
  expiryHeight := tx.header.expiryHeight
  inputs := (tx.transparent.vin.zip tx.scriptSigs).map fun (i, s) =>
    if i.prevout.IsNull then .coinbase 1 [] i.nSequence
    else .prevOut ⟨i.prevout.hash, i.prevout.n⟩ s i.nSequence
  outputs := tx.transparent.vout.map fun o => ⟨o.value, o.scriptPubKey⟩
  sapling :=
    let spends := tx.sapling.spends.map fun s => (⟨s.cv, s.nullifier, s.rk, s.zkproof,
      s.spendAuthSig⟩ : Native.SaplingSpend)
    let outputs := tx.sapling.outputs.map fun o => (⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext,
      o.outCiphertext, o.zkproof⟩ : Native.SaplingOutput)
    match spends, outputs with
    | [], [] => none
    | sp :: sps, os => some ⟨tx.sapling.valueBalance,
        .spendsAndMaybeOutputs tx.sapling.anchor ⟨sp, sps⟩ os, tx.sapling.bindingSig⟩
    | [], o :: os => some ⟨tx.sapling.valueBalance, .justOutputs ⟨o, os⟩, tx.sapling.bindingSig⟩
  orchard := orchardData tx.orchard
  ironwood := match tx.format with | .v5 => none | .v6 iw => orchardData iw
where
  /-- An Orchard-shaped component, only when it has an Action. -/
  orchardData (b : OrchardBundle) : Option Native.OrchardData :=
    match b.actions.map fun a => (⟨a.cv, a.nullifier, a.rk, a.cmx, a.ephemeralKey,
        a.encCiphertext, a.outCiphertext, a.spendAuthSig⟩ : Native.Action) with
    | [] => none
    | a :: as => some ⟨b.flags, b.valueBalance, b.anchor, b.proofs, ⟨a, as⟩, b.bindingSig⟩

/-- The coins the inputs spend, as Zakura's previous outputs. -/
def previousOutputs (tx : Spec.Transaction) : List Native.Output :=
  tx.transparent.vin.map fun i => ⟨i.spent.value, i.spent.scriptPubKey⟩

/-- Whether Zakura's native code gives the vector's digests. -/
def checkNative (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some tx =>
    let p := toParts tx
    match Zip244SighashCache.new p (previousOutputs tx) with
    | none => false
    | some cache =>
      Native.txid p == some (hex v.txid) &&
      Native.authDigest (coinbaseScriptOf tx) p == some (hex v.authDigest) &&
      cache.sighash .all none == some (hex v.sighashShielded) &&
      match v.transparentInput with
      | none => true
      | some i => (hashTypes v).all fun (ht, expected) =>
        match expected with
        | some e => cache.sighash (.ofSpec ht) (some i) == some (hex e)
        -- No digest: `SIGHASH_SINGLE` without a corresponding output, which the callback
        -- refuses before calling the cache (`Proofs/Script.lean`).
        | none => !cache.hasCorrespondingOutput i

#guard zip244Vectors.map checkNative = List.replicate 10 true

/-- Whether Zakura's native code gives the version 6 vector's digests. -/
def checkNativeV6 (v : V6Vector) : Bool :=
  let p := toParts v.tx
  match Zip244SighashCache.new p (previousOutputs v.tx), hashHeaderOf p with
  | some cache, some header =>
    header == hex v.headerDigest &&
    Native.txid p == some (hex v.txid) &&
    (v.authDigest.all fun d => Native.authDigest (coinbaseScriptOf v.tx) p == some (hex d)) &&
    v.sighashShielded.all fun d => cache.sighash .all none == some (hex d)
  | _, _ => false
where
  /-- The header digest. -/
  hashHeaderOf (p : Parts) : Option Blake2bHash := Native.hashHeader p

#guard v6Vectors.map checkNativeV6 = [true, true]

/-! ## A coinbase input's `scriptSig` -/

/-- A `push_num` that writes the height's low byte after a one-byte push, and a genesis script:
    enough to tell the cases of `Input::coinbase_script` apart. -/
def testCoinbaseScript : CoinbaseScript :=
  ⟨fun h => [0x01, h.setWidth 8], [0x04, 0xff, 0xff, 0x00, 0x1d]⟩

-- A coinbase input above genesis: `push_num(height)` then its data.
#guard (Native.Input.coinbase 0x2a [0xaa, 0xbb] 0).coinbaseScript testCoinbaseScript ==
  some [0x01, 0x2a, 0xaa, 0xbb]

-- The genesis coinbase input: its data is the whole genesis script.
#guard (Native.Input.coinbase 0 [0x04, 0xff, 0xff, 0x00, 0x1d] 0).coinbaseScript
    testCoinbaseScript == some [0x04, 0xff, 0xff, 0x00, 0x1d]

-- A height 0 input with other data has no `scriptSig` (`coinbase_script`'s `expect` panics).
#guard (Native.Input.coinbase 0 [0xaa] 0).coinbaseScript testCoinbaseScript == none

-- A non-coinbase input has none to rebuild.
#guard (Native.Input.prevOut ⟨List.Vector.replicate 32 1, 0⟩ [0xaa] 0).coinbaseScript
    testCoinbaseScript == none

/-! ## Version 4 -/

/-- A byte list as a vector of `n` bytes, zero-padded or cut. -/
def toVec (n : ℕ) (l : List Byte) : Bytes n :=
  ⟨(l ++ List.replicate n 0).take n, by simp⟩

/-- A decoded version 4 transaction as Zakura's parser holds it: a null prevout as a coinbase
    input, each component only when it is not empty. -/
def toV4 (tx : LegacyTransaction) : Native.V4.Transaction where
  inputs := tx.transparent.vin.map fun i =>
    if i.prevout.IsNull then .coinbase 1 [] i.nSequence
    else .prevOut ⟨i.prevout.hash, i.prevout.n⟩ [] i.nSequence
  outputs := tx.transparent.vout.map fun o => ⟨o.value, o.scriptPubKey⟩
  lockTime := tx.header.lockTime
  expiryHeight := tx.header.expiryHeight
  joinsplitData :=
    match tx.joinSplits.map fun js => (⟨js.vpubOld, js.vpubNew, js.anchor, js.nullifiers,
        js.commitments, js.ephemeralKey, js.randomSeed, js.macs, toVec 192 js.zkproof,
        js.encCiphertexts⟩ : Native.V4.JoinSplit) with
    | [] => none
    | js :: jss => some ⟨js, jss, tx.joinSplitPubKey, toVec 64 []⟩
  saplingShieldedData :=
    let spends := tx.saplingSpends.map fun s =>
      (⟨s.cv, s.anchor, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩ : Native.V4.Spend)
    let outputs := tx.saplingOutputs.map fun o => (⟨o.cv, o.cmu, o.ephemeralKey,
      o.encCiphertext, o.outCiphertext, o.zkproof⟩ : Native.SaplingOutput)
    match spends, outputs with
    | [], [] => none
    | sp :: sps, os => some ⟨tx.valueBalance, .spendsAndMaybeOutputs ⟨sp, sps⟩ os, toVec 64 []⟩
    | [], o :: os => some ⟨tx.valueBalance, .justOutputs ⟨o, os⟩, toVec 64 []⟩

/-- Whether Zakura's native code gives the ZIP 243 vector's signature digest, through
    `SigHasher::sighash_v4_raw`. -/
def checkNativeV4 (v : LegacyVector) : Bool :=
  let spent : List TxOut := match v.transparentInput with
    | none => []
    | some i => List.replicate i ⟨0, []⟩ ++ [⟨.ofNat _ v.amount, []⟩]
  match (legacyDecoder (.ofNat _ v.branch.id) spent).run' (hex v.tx) with
  | none => false
  | some tx =>
    let previous := tx.transparent.vin.map fun i => (⟨i.spent.value, []⟩ : Native.Output)
    match Native.V4.V4Sighash.new (toV4 tx) (some (.ofNat _ v.branch.id)) previous with
    | some (some s) =>
      Native.V4.sigHasherSighashV4Raw s (.ofNat _ v.hashType)
          (v.transparentInput.map fun i => (i, hex v.scriptCode)) ==
        some (hex v.sighash)
    | _ => false

#guard zip243Vectors.map checkNativeV4 = List.replicate 10 true

/-! ## Every hash-type byte, through the callback -/

/-- Whether, for each of the 256 bytes a signature can end with, Zakura's callback over its own
    `SigHasher` gives the vector's transparent input the specification's result: the digest, or
    no digest where ZIP 244 says validation fails (an undefined hash type, or `SIGHASH_SINGLE`
    without a corresponding output). -/
def checkEveryByte (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some tx =>
    match v.transparentInput, Zip244SighashCache.new (toParts tx) (previousOutputs tx) with
    | none, _ => true
    | some _, none => false
    | some i, some cache =>
      if h : i < tx.transparent.vin.length then
        (List.range 256).all fun n =>
          let b : Byte := .ofNat 8 n
          (Script.HashType.fromBits (b.setWidth 32) false).toOption.map (fun hashType =>
              Script.calculateSighash ⟨Native.sigHasherSighash cache, fun _ _ => none⟩ 5
                tx.transparent.vout.length i [] hashType) ==
            some (some ((transparentSighash? blake2b256 (tx.version blake2b256)
              tx.header.consensusBranchId (headerDigest blake2b256 tx.header)
              (saplingDigest blake2b256 tx.format tx.sapling) (tx.orchardDigest blake2b256)
              ⟨i, h⟩ b).map (·.toList)))
      else false

#guard zip244Vectors.map checkEveryByte = List.replicate 10 true

/-- Whether, for each of the 256 bytes a signature can end with, Zakura's callback over its own
    version 4 `SigHasher` gives the vector's transparent input ZIP 243's digest of that byte. -/
def checkEveryByteV4 (v : LegacyVector) : Bool :=
  let spent : List TxOut := match v.transparentInput with
    | none => []
    | some i => List.replicate i ⟨0, []⟩ ++ [⟨.ofNat _ v.amount, []⟩]
  match (legacyDecoder (.ofNat _ v.branch.id) spent).run' (hex v.tx), v.transparentInput with
  | none, _ => false
  | some _, none => true
  | some tx, some i =>
    let previous := tx.transparent.vin.map fun i => (⟨i.spent.value, []⟩ : Native.Output)
    match Native.V4.V4Sighash.new (toV4 tx) (some (.ofNat _ v.branch.id)) previous with
    | some (some s) =>
      if h : i < tx.transparent.vin.length then
        (List.range 256).all fun n =>
          let b : Byte := .ofNat 8 n
          (Script.HashType.fromBits (b.setWidth 32) false).toOption.map (fun hashType =>
              Script.calculateSighash ⟨fun _ _ => none, Native.V4.sigHasherSighashV4Raw s⟩ 4
                tx.transparent.vout.length i (hex v.scriptCode) hashType) ==
            some (some (some (legacySignatureDigest blake2b256 tx
              (.transparent b ⟨i, h⟩ (hex v.scriptCode))).toList))
      else false
    | _ => false

#guard zip243Vectors.map checkEveryByteV4 = List.replicate 10 true

/-! ## The block's auth data root (`src/block/merkle.rs`, lines 438–474) -/

-- `auth_data_padding`: three leaves have the root of the same leaves and a null fourth.
#guard Native.authDataRoot [List.replicate 32 0x42, List.replicate 32 0xaa,
    List.replicate 32 0x77] ==
  Native.authDataRoot [List.replicate 32 0x42, List.replicate 32 0xaa,
    List.replicate 32 0x77, List.replicate 32 0]

-- `auth_data_pre_v5`: a pre-version 5 transaction's leaf is the placeholder.
#guard Native.authDataRootOfTransactions [none] ==
  Native.authDataRoot [List.replicate 32 0xff]

/-! ## The transparent parser -/

/-- Whether Zakura's parser reads the vector's transparent inputs and outputs (after the
    version 5 header's 20 bytes) as the specification's decoder does. A vector with a coinbase
    input is skipped: its `scriptSig` does not start with a height, which Zakura rejects. -/
def checkParse (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some tx =>
    if tx.transparent.vin.any (decide ·.prevout.IsNull) then true
    else
      let parse : Native.Parser (List Native.Input × List Native.Output) := do
        let inputs ← Native.readVec (Native.readInput fun _ => [])
        let outputs ← Native.readVec Native.readOutput
        pure (inputs, outputs)
      match parse ((hex v.tx).drop 20) with
      | none => false
      | some ((inputs, outputs), _) =>
        inputs.map (·.prevoutSpec.encode) == tx.transparent.vin.map (·.prevout.encode) &&
        inputs.map (·.sequence) == tx.transparent.vin.map (·.nSequence) &&
        inputs.map (·.scriptSig (coinbaseScriptOf tx)) == tx.scriptSigs &&
        outputs.map (fun o => (o.value, o.lockScript)) ==
          tx.transparent.vout.map fun o => (o.value, o.scriptPubKey)

#guard zip244Vectors.map checkParse = List.replicate 10 true

/-- `push_num(h).to_bytes()` for a height, BIP 34's minimal encoding: `OP_0`, `OP_1` to
    `OP_16`, or a push of the little-endian bytes, with a zero byte if the top bit is set. -/
def testPushNum (h : ℕ) : List Byte :=
  if h = 0 then [0]
  else if h ≤ 16 then [BitVec.ofNat 8 (0x50 + h)]
  else
    let bytes := ((List.range 5).map fun j => BitVec.ofNat 8 (h / 256 ^ j)).reverse.dropWhile
      (· = 0) |>.reverse
    let bytes := if bytes.getLast?.any (0x80 ≤ ·.toNat) then bytes ++ [0] else bytes
    BitVec.ofNat 8 bytes.length :: bytes

/-- A coinbase input's encoding: the null outpoint, its `scriptSig`, sequence number 1. -/
def coinbaseInputBytes (scriptSig : List Byte) : List Byte :=
  List.replicate 32 0 ++ List.replicate 4 0xff ++ [BitVec.ofNat 8 scriptSig.length] ++ scriptSig ++
    [1, 0, 0, 0]

/-- Whether the parser reads a coinbase input of height `h` and data `d` from `scriptSig`, and
    `coinbase_script` rebuilds that `scriptSig`. -/
def checkCoinbase (scriptSig : List Byte) (h : BitVec 32) (d : List Byte) : Bool :=
  let cs : CoinbaseScript := ⟨fun h => testPushNum h.toNat, Native.GENESIS_COINBASE_SCRIPT_SIG⟩
  match Native.readInput testPushNum (coinbaseInputBytes scriptSig) with
  | some (input@(.coinbase h' d' q), []) =>
    h' == h && d' == d && q == 1 && input.coinbaseScript cs == some scriptSig
  | _ => false

-- Height 300 (`02 2c 01`), then two bytes of data.
#guard checkCoinbase (testPushNum 300 ++ [0xaa, 0xbb]) 300 [0xaa, 0xbb]

-- Height 5 (`OP_5`), then data.
#guard checkCoinbase (testPushNum 5 ++ [0xcc]) 5 [0xcc]

-- The genesis `scriptSig`: height 0, the whole script as data.
#guard checkCoinbase Native.GENESIS_COINBASE_SCRIPT_SIG 0 Native.GENESIS_COINBASE_SCRIPT_SIG

-- A non-canonical height (5 pushed as one byte, not `OP_5`) is rejected.
#guard (Native.readInput testPushNum (coinbaseInputBytes [1, 5, 0xcc])).isNone

-- A height of 0 that is not the genesis `scriptSig` is rejected.
#guard (Native.readInput testPushNum (coinbaseInputBytes [0, 0xcc])).isNone

-- A `scriptSig` of one byte is shorter than `MIN_COINBASE_SCRIPT_LEN`.
#guard (Native.readInput testPushNum (coinbaseInputBytes [0x55])).isNone

end ZcashSighash.Tests
