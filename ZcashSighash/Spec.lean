/-
# Zcash Transaction Signature Digests

* The version 5 transaction identifier and signature digests (ZIP 244, §T and §S).
* Their version 6 forms (ZIP 229).
* The transparent signature check.

The header, Sapling, Orchard and Ironwood digests are inputs.
-/
module

public import Mathlib.Data.Vector.Basic

@[expose] public section

namespace ZcashSighash.Spec

/-! ## Bytes and BLAKE2b-256 -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- A BLAKE2b-256 output. -/
abbrev Digest := List.Vector Byte 32

/-- A BLAKE2b personalization. -/
abbrev Personalization := List.Vector Byte 16

/-- `BLAKE2b-256(p, x)`. -/
abbrev Hash := Personalization → List Byte → Digest

/-- The bytes of an ASCII string of length `n`. -/
def ascii (s : String) (n : ℕ) (h : s.toList.length = n := by decide) : List.Vector Byte n :=
  ⟨s.toList.map fun c => BitVec.ofNat 8 c.toNat, by simpa using h⟩

/-- A personalization, written as its 16 ASCII characters. -/
abbrev personal (s : String) (h : s.toList.length = 16 := by decide) : Personalization :=
  ascii s 16 h

/-- `I2LEOSP_ℓ(x)` (§5.1). -/
def I2LEOSP (ℓ x : ℕ) : List Byte :=
  (List.range ((ℓ + 7) / 8)).map fun j => BitVec.ofNat 8 (x / 256 ^ j)

/-- A `uint32`, little-endian. -/
def u32 (x : BitVec 32) : List Byte := I2LEOSP 32 x.toNat

/-- An `int64`, two's complement, little-endian. -/
def i64 (x : BitVec 64) : List Byte := I2LEOSP 64 x.toNat

/-- `compactSize`.

**Not stated in the specification.** §7.1 uses this type without defining it; this is
Bitcoin's encoding, as zcashd's `WriteCompactSize` writes it. -/
def compactSize (n : BitVec 64) : List Byte :=
  if n.toNat < 0xfd then I2LEOSP 8 n.toNat
  else if n.toNat ≤ 0xffff then 0xfd :: I2LEOSP 16 n.toNat
  else if n.toNat ≤ 0xffffffff then 0xfe :: I2LEOSP 32 n.toNat
  else 0xff :: I2LEOSP 64 n.toNat

/-- A script's field encoding: its length, then its bytes. -/
def script (s : List Byte) : List Byte := compactSize (BitVec.ofNat 64 s.length) ++ s

/-! ## Transparent inputs and outputs -/

/-- An `outpoint`. -/
structure OutPoint where
  hash : List.Vector Byte 32
  n : BitVec 32

/-- An `outpoint`'s field encoding. -/
def OutPoint.encode (o : OutPoint) : List Byte := o.hash.toList ++ u32 o.n

/-- A null `prevout` (§3.11).

**Not stated in the specification.** A zero hash and the index `0xffffffff`, as zcashd's
`BaseOutPoint::IsNull` decides. -/
def OutPoint.IsNull (o : OutPoint) : Prop :=
  o.hash.toList = List.replicate 32 0 ∧ o.n = 0xffffffff

instance (o : OutPoint) : Decidable o.IsNull := by unfold OutPoint.IsNull; infer_instance

/-- A transparent output. -/
structure TxOut where
  value : BitVec 64
  scriptPubKey : List Byte

/-- A transparent output's field encoding. -/
def TxOut.encode (o : TxOut) : List Byte := i64 o.value ++ script o.scriptPubKey

/-- A transparent input, with the coin it spends (§S.2c, §S.2d, §S.2g). -/
structure TxIn where
  prevout : OutPoint
  nSequence : BitVec 32
  spent : TxOut

/-- A transaction's transparent inputs and outputs. -/
structure Transparent where
  vin : List TxIn
  vout : List TxOut

/-- > A transaction that has a single transparent input with a null `prevout` field, is called a
    > coinbase transaction. (§3.11) -/
def Transparent.IsCoinbase (t : Transparent) : Prop := ∃ i, t.vin = [i] ∧ i.prevout.IsNull

instance (t : Transparent) : Decidable t.IsCoinbase := by
  unfold Transparent.IsCoinbase
  match t.vin with
  | [] => exact isFalse (by simp)
  | [i] => exact if h : i.prevout.IsNull then isTrue ⟨i, rfl, h⟩ else isFalse (by simpa using h)
  | _ :: _ :: _ => exact isFalse (by simp)

/-! ## Hash types (§S.2a) -/

/-- `SIGHASH_ALL`, `SIGHASH_NONE` or `SIGHASH_SINGLE`. -/
inductive Base where
  | all
  | none
  | single
  deriving DecidableEq

/-- A hash type: its base, with or without `SIGHASH_ANYONECANPAY`. -/
structure HashType where
  base : Base
  anyoneCanPay : Bool
  deriving DecidableEq

/-- > `SIGHASH_ALL` (0x01), `SIGHASH_NONE` (0x02), and `SIGHASH_SINGLE` (0x03), with or without
    > the `SIGHASH_ANYONECANPAY` flag (0x80) -/
def HashType.toByte (h : HashType) : Byte :=
  (match h.base with | .all => 0x01 | .none => 0x02 | .single => 0x03) |||
    if h.anyoneCanPay then 0x80 else 0

/-- The hash type a byte encodes; `none` for an undefined one (not 0x01, 0x02, 0x03, 0x81, 0x82
    or 0x83). -/
def HashType.ofByte? (b : Byte) : Option HashType :=
  let base : Option Base :=
    match b &&& 0x7f with
    | 0x01 => some .all
    | 0x02 => some .none
    | 0x03 => some .single
    | _ => none
  base.map fun base => ⟨base, b &&& 0x80 != 0⟩

/-- A Sapling Spend or Orchard Action, or a transparent input with its hash type. -/
inductive SignableInput (t : Transparent) where
  | shielded
  | transparent (hashType : HashType) (index : Fin t.vin.length)

/-- > If we are producing a hash for the signature over a Sapling Spend or an Orchard Action,
    > `hash_type` is set to `SIGHASH_ALL`. -/
def SignableInput.hashType {t : Transparent} : SignableInput t → HashType
  | .shielded => ⟨.all, false⟩
  | .transparent h _ => h

/-- §S.2a's restriction besides an undefined hash type:
    > Using `SIGHASH_SINGLE` without a "corresponding output" (an output with the same index as
    > the input being verified). -/
def SignableInput.Restrictions {t : Transparent} : SignableInput t → Prop
  | .shielded => True
  | .transparent h i => h.base = .single → i.val < t.vout.length

instance {t : Transparent} (input : SignableInput t) : Decidable input.Restrictions := by
  cases input <;> unfold SignableInput.Restrictions <;> infer_instance

/-! ## Digests -/

section
variable (H : Hash)

/-- A node of the digest tree: the hash of its children, in order. -/
def node (p : Personalization) (children : List Digest) : Digest :=
  H p (children.flatMap (·.toList))

variable (t : Transparent)

/-- §T.2a. -/
def prevoutsDigest : Digest :=
  H (personal "ZTxIdPrevoutHash") (t.vin.flatMap (·.prevout.encode))

/-- §T.2b. -/
def sequenceDigest : Digest :=
  H (personal "ZTxIdSequencHash") (t.vin.flatMap (u32 ·.nSequence))

/-- §T.2c. -/
def outputsDigest : Digest :=
  H (personal "ZTxIdOutputsHash") (t.vout.flatMap TxOut.encode)

/-- §T.2. -/
def transparentDigest : Digest :=
  if t.vin.isEmpty && t.vout.isEmpty then H (personal "ZTxIdTranspaHash") []
  else node H (personal "ZTxIdTranspaHash")
    [prevoutsDigest H t, sequenceDigest H t, outputsDigest H t]

/-- §S.2b. -/
def prevoutsSigDigest (h : HashType) : Digest :=
  if h.anyoneCanPay then H (personal "ZTxIdPrevoutHash") [] else prevoutsDigest H t

/-- §S.2c. -/
def amountsSigDigest (h : HashType) : Digest :=
  H (personal "ZTxTrAmountsHash")
    (if h.anyoneCanPay then [] else t.vin.flatMap (i64 ·.spent.value))

/-- §S.2d. -/
def scriptPubKeysSigDigest (h : HashType) : Digest :=
  H (personal "ZTxTrScriptsHash")
    (if h.anyoneCanPay then [] else t.vin.flatMap (script ·.spent.scriptPubKey))

/-- §S.2e. -/
def sequenceSigDigest (h : HashType) : Digest :=
  if h.anyoneCanPay then H (personal "ZTxIdSequencHash") [] else sequenceDigest H t

variable {t}

/-- §S.2f. -/
def outputsSigDigest (input : SignableInput t) : Digest :=
  match input.hashType.base, input with
  | .all, _ => outputsDigest H t
  | .single, .transparent _ i =>
    match t.vout[i.val]? with
    | some o => H (personal "ZTxIdOutputsHash") o.encode
    | none => H (personal "ZTxIdOutputsHash") []
  | _, _ => H (personal "ZTxIdOutputsHash") []

/-- §S.2g. -/
def txinSigDigest : SignableInput t → Digest
  | .shielded => H (personal "Zcash___TxInHash") []
  | .transparent _ i =>
    let txin := t.vin[i]
    H (personal "Zcash___TxInHash")
      (txin.prevout.encode ++ i64 txin.spent.value ++ script txin.spent.scriptPubKey ++
        u32 txin.nSequence)

/-- §S.2. -/
def transparentSigDigest (input : SignableInput t) : Digest :=
  if t.IsCoinbase ∨ t.vin = [] then transparentDigest H t
  else
    let h := input.hashType
    H (personal "ZTxIdTranspaHash")
      (h.toByte :: [prevoutsSigDigest H t h, amountsSigDigest H t h,
        scriptPubKeysSigDigest H t h, sequenceSigDigest H t h, outputsSigDigest H input,
        txinSigDigest H input].flatMap (·.toList))

/-- `"ZcashTxHash_" || CONSENSUS_BRANCH_ID`. -/
def txHashPersonalization (branchId : BitVec 32) : Personalization :=
  ⟨(ascii "ZcashTxHash_" 12).toList ++ u32 branchId, by simp [ascii, u32, I2LEOSP]⟩

/-- A version 5 or version 6 transaction, with the version 6 Ironwood digest. -/
inductive Version where
  | v5
  | v6 (ironwood : Digest)

/-- §S; for version 6, ZIP 229.

**Not stated in the specification.** ZIP 229 adds the Ironwood digest to the version 6 signature
digest without saying where; it places it last in the transaction identifier and auth digest,
as here. -/
def signatureDigest (v : Version) (branchId : BitVec 32) (header sapling orchard : Digest)
    (input : SignableInput t) : Digest :=
  node H (txHashPersonalization branchId)
    ([header, transparentSigDigest H input, sapling, orchard] ++
      match v with | .v5 => [] | .v6 ironwood => [ironwood])

/-- §T; for version 6, ZIP 229 (the Ironwood digest last). -/
def txidDigest (t : Transparent) (v : Version) (branchId : BitVec 32)
    (header sapling orchard : Digest) : Digest :=
  node H (txHashPersonalization branchId)
    ([header, transparentDigest H t, sapling, orchard] ++
      match v with | .v5 => [] | .v6 ironwood => [ironwood])

/-! ## The signature check -/

/-- The digest a signature over the transparent input `i` signs, given the hash-type byte `b` it
    carries: `none` when §S.2a's restrictions fail. `branchId` is that of the network upgrade
    active at the block's height (§7.1.2). -/
def transparentSighash? (v : Version) (branchId : BitVec 32) (header sapling orchard : Digest)
    (i : Fin t.vin.length) (b : Byte) : Option Digest := do
  let h ← HashType.ofByte? b
  let input := SignableInput.transparent h i
  if input.Restrictions then some (signatureDigest H v branchId header sapling orchard input)
  else none

/-- `OP_CHECKSIG`'s signature check: a digest exists and `verify` accepts the signature on it.

**Not stated in the specification.** §S.2a's "validation failure" makes only this check false,
not the transaction invalid, as Zebra and Zakura do. -/
def checkSig (verify : Digest → Bool) (digest? : Option Digest) : Bool := digest?.any verify

end

end ZcashSighash.Spec
