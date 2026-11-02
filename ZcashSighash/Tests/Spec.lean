/-
The specification on ZIP 244's test vectors, with BLAKE2b: each transaction, decoded from its
version 5 encoding (ZIP 225), has the vector's identifier and auth digest, and its inputs the
vector's signature digests. Where a vector has no `SIGHASH_SINGLE` digest, the input has no
corresponding output, and the signature check finds no digest. Likewise two version 6
transactions from the crates' tests, with the digests the tests give.
-/
import ZcashSighash.Spec
import ZcashSighash.Verifier.Encoding
import ZcashSighash.Tests.Zip244

namespace ZcashSighash.Tests

open ZcashSighash.Spec
open ZcashSighash.Verifier (blake2b256)

/-- The bytes a hex string writes. -/
def hex (s : String) : List Byte :=
  let digit (c : Char) : ℕ := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (16 * digit a + digit b) :: go rest
    | _ => []
  go s.toList

/-! ## Decoding a version 5 transaction (ZIP 225) -/

/-- A decoder: the bytes left, or a failure. -/
abbrev Decoder := StateT (List Byte) Option

/-- `n` bytes. -/
def bytes (n : ℕ) : Decoder (List Byte) := do
  let s ← get
  if s.length < n then failure
  set (s.drop n)
  pure (s.take n)

/-- `n` bytes, as a vector. -/
def vec (n : ℕ) : Decoder (Bytes n) := do
  let b ← bytes n
  if h : b.length = n then pure ⟨b, h⟩ else failure

/-- A little-endian unsigned integer of `n` bytes. -/
def uint (n : ℕ) : Decoder ℕ := do
  let b ← bytes n
  pure ((b.zipIdx.map fun (x, i) => x.toNat * 256 ^ i).sum)

/-- A `compactSize`. -/
def compactSize : Decoder ℕ := do
  match (← uint 1) with
  | 0xfd => uint 2
  | 0xfe => uint 4
  | 0xff => uint 8
  | n => pure n

/-- `n` items. -/
def many {α : Type} (n : ℕ) (d : Decoder α) : Decoder (List α) :=
  (List.range n).mapM fun _ => d

/-- A script: a `compactSize` length, then its bytes. -/
def script : Decoder (List Byte) := do bytes (← compactSize)

/-- A version 5 transaction, with the coins its inputs spend. -/
def decoder (spent : List TxOut) : Decoder Transaction := do
  let header : Header := ⟨.ofNat _ (← uint 4), .ofNat _ (← uint 4), .ofNat _ (← uint 4),
    .ofNat _ (← uint 4), .ofNat _ (← uint 4)⟩
  let vin ← many (← compactSize) do
    pure (← vec 32, BitVec.ofNat 32 (← uint 4), ← script, BitVec.ofNat 32 (← uint 4))
  let vout ← many (← compactSize) do
    pure ({ value := .ofNat _ (← uint 8), scriptPubKey := ← script } : TxOut)
  let spendsCore ← many (← compactSize) do pure (← vec 32, ← vec 32, ← vec 32)
  let outputsCore ← many (← compactSize) do
    pure (← vec 32, ← vec 32, ← vec 32, ← vec 580, ← vec 80)
  let nSapling := spendsCore.length + outputsCore.length
  let valueBalance ← if nSapling > 0 then BitVec.ofNat 64 <$> uint 8 else pure 0
  let anchor ← if spendsCore.length > 0 then vec 32 else pure (List.Vector.replicate 32 0)
  let spendProofs ← many spendsCore.length (vec 192)
  let spendSigs ← many spendsCore.length (vec 64)
  let outputProofs ← many outputsCore.length (vec 192)
  let bindingSig ← if nSapling > 0 then vec 64 else pure (List.Vector.replicate 64 0)
  let actionsCore ← many (← compactSize) do
    pure (← vec 32, ← vec 32, ← vec 32, ← vec 32, ← vec 32, ← vec 580, ← vec 80)
  let n := actionsCore.length
  let flags ← if n > 0 then (fun b : List Byte => b.headD 0) <$> bytes 1 else pure 0
  let valueBalanceOrchard ← if n > 0 then BitVec.ofNat 64 <$> uint 8 else pure 0
  let anchorOrchard ← if n > 0 then vec 32 else pure (List.Vector.replicate 32 0)
  let proofs ← if n > 0 then bytes (← compactSize) else pure []
  let actionSigs ← many n (vec 64)
  let bindingSigOrchard ← if n > 0 then vec 64 else pure (List.Vector.replicate 64 0)
  if (← get) ≠ [] then failure
  let spends := (spendsCore.zip (spendProofs.zip spendSigs)).map
    fun ((cv, nf, rk), (proof, sig)) => (⟨cv, nf, rk, proof, sig⟩ : SaplingSpend)
  let outputs := (outputsCore.zip outputProofs).map
    fun ((cv, cmu, epk, enc, out), proof) => (⟨cv, cmu, epk, enc, out, proof⟩ : SaplingOutput)
  let actions := (actionsCore.zip actionSigs).map
    fun ((cv, nf, rk, cmx, epk, enc, out), sig) => (⟨cv, nf, rk, cmx, epk, enc, out, sig⟩ : Action)
  let txins := (vin.zip (spent ++ List.replicate vin.length (⟨0, []⟩ : TxOut))).map
    fun ((hash, n, _, seq), coin) => (⟨⟨hash, n⟩, seq, coin⟩ : TxIn)
  pure
    { format := .v5, header, transparent := ⟨txins, vout⟩
      scriptSigs := vin.map fun (_, _, s, _) => s
      sapling := ⟨spends, outputs, valueBalance, anchor, bindingSig⟩
      orchard := ⟨actions, flags, valueBalanceOrchard, anchorOrchard, proofs, bindingSigOrchard⟩ }

/-- A version 5 transaction's encoding, decoded, with the coins its inputs spend. -/
def decode (b : List Byte) (spent : List TxOut) : Option Transaction := (decoder spent).run' b

/-! ## The checks -/

/-- Each hash type, with the vector's digest for it. -/
def hashTypes (v : Zip244Vector) : List (HashType × Option String) :=
  [(⟨.all, false⟩, v.sighashAll), (⟨.none, false⟩, v.sighashNone),
    (⟨.single, false⟩, v.sighashSingle), (⟨.all, true⟩, v.sighashAllAnyone),
    (⟨.none, true⟩, v.sighashNoneAnyone), (⟨.single, true⟩, v.sighashSingleAnyone)]

/-- Whether the specification gives the vector's digests: its identifier, auth digest and
    shielded signature digest, and for its transparent input, each hash type's signature
    digest, or no digest from `transparentSighash?` where the vector has none. -/
def check (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some tx =>
    (tx.txid blake2b256).toList == hex v.txid &&
    (tx.authDigest blake2b256).toList == hex v.authDigest &&
    (tx.signatureDigest blake2b256 .shielded).toList == hex v.sighashShielded &&
    match v.transparentInput with
    | none => true
    | some i =>
      if h : i < tx.transparent.vin.length then
        (hashTypes v).all fun (ht, expected) =>
          (transparentSighash? blake2b256 (tx.version blake2b256) tx.header.consensusBranchId
              (headerDigest blake2b256 tx.header) (saplingDigest blake2b256 tx.format tx.sapling)
              (tx.orchardDigest blake2b256) ⟨i, h⟩ ht.toByte).map (·.toList) ==
            expected.map hex
      else false

#guard zip244Vectors.length = 10

#guard zip244Vectors.map check = List.replicate 10 true

/-! ## Version 6

ZIP 229 has no test vectors. The crates have two version 6 transactions whose digests were
computed independently with Python's `hashlib.blake2b`. -/

/-- No Sapling Spends or Outputs. -/
def noSapling : Sapling := ⟨[], [], 0, List.Vector.replicate 32 0, List.Vector.replicate 64 0⟩

/-- No Orchard or Ironwood Actions. -/
def noActions : OrchardBundle :=
  ⟨[], 0, 0, List.Vector.replicate 32 0, [], List.Vector.replicate 64 0⟩

/-- A version 6 transaction from a crate's test, with the digests the test gives. -/
structure V6Vector where
  tx : Transaction
  headerDigest : String
  txid : String
  authDigest : Option String
  sighashShielded : Option String

/-- The two version 6 transactions. -/
def v6Vectors : List V6Vector := [
  /- No transparent or shielded parts, under NU7's branch ID: `zcash_primitives` 0.31.0's
     `nu7_v6_encoding_and_digests_are_feature_independent` (`src/transaction/tests.rs`, lines
     44–118). -/
  ⟨{ format := .v6 noActions, header := ⟨0x80000006, 0xD884B698, 0x77190AD9, 0, 1⟩,
      transparent := ⟨[], []⟩, scriptSigs := [], sapling := noSapling, orchard := noActions },
    "199b8446da5a9247711a94527997d7e87c31dfe5e8efb4b34d020a2aee8ee1c5",
    "78296c68a370c2e1f058d997c81c7b011c4562c52fc5ca2994ad59cd179fbe9e", none,
    some "78296c68a370c2e1f058d997c81c7b011c4562c52fc5ca2994ad59cd179fbe9e"⟩,
  /- One transparent input, spending output 0 of the zero txid with an empty `scriptSig`, and one
     output of 50000 zatoshis to the script `OP_1`: `zakura-primitives` 4.0.0's
     `v6_encoding_hashes_and_fee_are_independent_of_nu7_cfg` (`src/transaction/tests.rs`, lines
     55–93). Its coin is not given, so neither is its signature digest. -/
  ⟨{ format := .v6 noActions, header := ⟨0x80000006, 0xD884B698, 0x37A5165B, 1, 2⟩,
      transparent := ⟨[⟨⟨List.Vector.replicate 32 0, 0⟩, 0xffffffff, ⟨0, []⟩⟩], [⟨50000, [0x51]⟩]⟩,
      scriptSigs := [[]], sapling := noSapling, orchard := noActions },
    "434bc31eb5d67ac6b935ab85cb0aabc06b079c39f8f4e1b50a6048372b3bfa2d",
    "e11e16887d9aea199fc4eaa3b371c6868ded3e9a2b1c3393a7b0c15f79e73179",
    some "454423cf6de9acb289a60852144679176cea3bd5e5ec51526d483ced2533e73a", none⟩]

/-- Whether the specification gives the vector's digests. -/
def checkV6 (v : V6Vector) : Bool :=
  (headerDigest blake2b256 v.tx.header).toList == hex v.headerDigest &&
  (v.tx.txid blake2b256).toList == hex v.txid &&
  (v.authDigest.all fun d => (v.tx.authDigest blake2b256).toList == hex d) &&
  v.sighashShielded.all fun d => (v.tx.signatureDigest blake2b256 .shielded).toList == hex d

#guard v6Vectors.map checkV6 = [true, true]

end ZcashSighash.Tests
