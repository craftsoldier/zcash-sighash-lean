/-
# Zcash Transaction Digests

* The version 5 transaction identifier, signature and auth digests (ZIP 244, §T, §S and §A).
* Their version 6 forms (ZIP 229).
* The transparent signature check.

The signature and identifier digests are first stated over the header, Sapling, Orchard and
Ironwood digests, then over a transaction's fields.
-/
module

public import Mathlib.Data.Vector.Basic

@[expose] public section

namespace ZcashSighash.Spec

/-! ## Bytes and BLAKE2b-256 -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- `n` bytes. -/
abbrev Bytes (n : ℕ) := List.Vector Byte n

/-- A BLAKE2b-256 output. -/
abbrev Digest := Bytes 32

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

/-! ## The header, Sapling, Orchard and Ironwood -/

/-- The header fields (§T.1). -/
structure Header where
  /-- With the `fOverwintered` flag. -/
  version : BitVec 32
  versionGroupId : BitVec 32
  consensusBranchId : BitVec 32
  lockTime : BitVec 32
  expiryHeight : BitVec 32

/-- A Sapling Spend. -/
structure SaplingSpend where
  cv : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  zkproof : Bytes 192
  spendAuthSig : Bytes 64

/-- A Sapling Output. -/
structure SaplingOutput where
  cv : Bytes 32
  cmu : Bytes 32
  ephemeralKey : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  zkproof : Bytes 192

/-- A transaction's Sapling Spends and Outputs. Its value balance and binding signature are
    used only when it has a Spend or an Output, and its anchor only when it has a Spend, as the
    transaction encoding holds them. -/
structure Sapling where
  spends : List SaplingSpend
  outputs : List SaplingOutput
  valueBalance : BitVec 64
  anchor : Bytes 32
  bindingSig : Bytes 64

/-- An Orchard Action. -/
structure Action where
  cv : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  cmx : Bytes 32
  ephemeralKey : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  spendAuthSig : Bytes 64

/-- A transaction's Orchard Actions, or its Ironwood ones, which have "the same structure"
    (ZIP 229). Its other fields are used only when it has an Action, as the transaction
    encoding holds them. -/
structure OrchardBundle where
  actions : List Action
  flags : Byte
  valueBalance : BitVec 64
  anchor : Bytes 32
  proofs : List Byte
  bindingSig : Bytes 64

/-- A transaction format: version 5, or version 6 with its Ironwood Actions (ZIP 229). -/
inductive Format where
  | v5
  | v6 (ironwood : OrchardBundle)

/-- Whether the format is version 6. -/
def Format.IsV6 : Format → Bool
  | .v5 => false
  | .v6 _ => true

/-- A version 5 or 6 transaction. -/
structure Transaction where
  format : Format
  header : Header
  transparent : Transparent
  /-- The `scriptSig` of each transparent input, in order. -/
  scriptSigs : List (List Byte)
  sapling : Sapling
  orchard : OrchardBundle

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

/-! ## The header, Sapling, Orchard and Ironwood digests -/

/-- §T.1. -/
def headerDigest (h : Header) : Digest :=
  H (personal "ZTxIdHeadersHash")
    (u32 h.version ++ u32 h.versionGroupId ++ u32 h.consensusBranchId ++ u32 h.lockTime ++
      u32 h.expiryHeight)

/-- §T.3a.i. -/
def saplingSpendsCompactDigest (s : Sapling) : Digest :=
  H (personal "ZTxIdSSpendCHash") (s.spends.flatMap (·.nullifier.toList))

/-- §T.3a.ii; for version 6 without the anchor (ZIP 229). -/
def saplingSpendsNoncompactDigest (f : Format) (s : Sapling) : Digest :=
  if f.IsV6 then
    H (personal "ZTxIdSSpendNH_v6") (s.spends.flatMap fun sp => sp.cv.toList ++ sp.rk.toList)
  else
    H (personal "ZTxIdSSpendNHash")
      (s.spends.flatMap fun sp => sp.cv.toList ++ s.anchor.toList ++ sp.rk.toList)

/-- §T.3a. -/
def saplingSpendsDigest (f : Format) (s : Sapling) : Digest :=
  if s.spends = [] then H (personal "ZTxIdSSpendsHash") []
  else node H (personal "ZTxIdSSpendsHash")
    [saplingSpendsCompactDigest H s, saplingSpendsNoncompactDigest H f s]

/-- §T.3b.i. -/
def saplingOutputsCompactDigest (s : Sapling) : Digest :=
  H (personal "ZTxIdSOutC__Hash")
    (s.outputs.flatMap fun o =>
      o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52)

/-- §T.3b.ii. -/
def saplingOutputsMemosDigest (s : Sapling) : Digest :=
  H (personal "ZTxIdSOutM__Hash")
    (s.outputs.flatMap fun o => (o.encCiphertext.toList.drop 52).take 512)

/-- §T.3b.iii. -/
def saplingOutputsNoncompactDigest (s : Sapling) : Digest :=
  H (personal "ZTxIdSOutN__Hash")
    (s.outputs.flatMap fun o =>
      o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)

/-- §T.3b. -/
def saplingOutputsDigest (s : Sapling) : Digest :=
  if s.outputs = [] then H (personal "ZTxIdSOutputHash") []
  else node H (personal "ZTxIdSOutputHash")
    [saplingOutputsCompactDigest H s, saplingOutputsMemosDigest H s,
      saplingOutputsNoncompactDigest H s]

/-- §T.3; for version 6, ZIP 229. -/
def saplingDigest (f : Format) (s : Sapling) : Digest :=
  if s.spends = [] ∧ s.outputs = [] then H (personal "ZTxIdSaplingHash") []
  else H (personal "ZTxIdSaplingHash")
    ((saplingSpendsDigest H f s).toList ++ (saplingOutputsDigest H s).toList ++
      i64 s.valueBalance)

/-- The personalizations of an Orchard-shaped digest tree, at its root, its three action
    digests, and its auth digest. -/
structure Personalizations where
  bundle : Personalization
  compact : Personalization
  memos : Personalization
  noncompact : Personalization
  auth : Personalization

/-- Orchard in version 5 (§T.4, §A.3). -/
def orchardV5 : Personalizations :=
  ⟨personal "ZTxIdOrchardHash", personal "ZTxIdOrcActCHash", personal "ZTxIdOrcActMHash",
    personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaHash"⟩

/-- Orchard in version 6 (ZIP 229). -/
def orchardV6 : Personalizations :=
  ⟨personal "ZTxIdOrchardH_v6", personal "ZTxIdOrcActCHash", personal "ZTxIdOrcActMHash",
    personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaH_v6"⟩

/-- Ironwood (ZIP 229). -/
def ironwoodV6 : Personalizations :=
  ⟨personal "ZTxIdIronwd_H_v6", personal "ZTxIdIrnActCH_v6", personal "ZTxIdIrnActMH_v6",
    personal "ZTxIdIrnActNH_v6", personal "ZTxAuthIrnwdH_v6"⟩

/-- §T.4, with the personalizations `p`; with `v6`, without the anchor (ZIP 229).

**Not stated in the specification.** ZIP 229 gives the digest of no Ironwood Actions under
`ironwoodV6`; with no Orchard Actions in version 6, this is the same rule under `orchardV6`. -/
def actionsDigest (p : Personalizations) (v6 : Bool) (b : OrchardBundle) : Digest :=
  if b.actions = [] then H p.bundle []
  else H p.bundle
    ((H p.compact (b.actions.flatMap fun a => a.nullifier.toList ++ a.cmx.toList ++
        a.ephemeralKey.toList ++ a.encCiphertext.toList.take 52)).toList ++
      (H p.memos (b.actions.flatMap fun a => (a.encCiphertext.toList.drop 52).take 512)).toList ++
      (H p.noncompact (b.actions.flatMap fun a => a.cv.toList ++ a.rk.toList ++
        a.encCiphertext.toList.drop 564 ++ a.outCiphertext.toList)).toList ++
      b.flags :: i64 b.valueBalance ++ if v6 then [] else b.anchor.toList)

/-- §A.1. -/
def transparentScriptsDigest (scriptSigs : List (List Byte)) : Digest :=
  H (personal "ZTxAuthTransHash") (scriptSigs.flatMap script)

/-- §A.2; for version 6, ZIP 229.

**Not stated in the specification.** ZIP 229 gives the digest of an empty Ironwood component
under its own personalization; with no Sapling Spends or Outputs in version 6, this is the same
rule under `ZTxAuthSapliH_v6`. -/
def saplingAuthDigest (f : Format) (s : Sapling) : Digest :=
  let p := if f.IsV6 then personal "ZTxAuthSapliH_v6" else personal "ZTxAuthSapliHash"
  if s.spends = [] ∧ s.outputs = [] then H p []
  else H p
    (s.spends.flatMap (·.zkproof.toList) ++ s.spends.flatMap (·.spendAuthSig.toList) ++
      s.outputs.flatMap (·.zkproof.toList) ++ s.bindingSig.toList ++
      if f.IsV6 ∧ s.spends ≠ [] then s.anchor.toList else [])

/-- §A.3, with the personalizations `p`; with `v6`, with the anchor (ZIP 229). -/
def actionsAuthDigest (p : Personalizations) (v6 : Bool) (b : OrchardBundle) : Digest :=
  if b.actions = [] then H p.auth []
  else H p.auth
    (b.proofs ++ b.actions.flatMap (·.spendAuthSig.toList) ++ b.bindingSig.toList ++
      if v6 then b.anchor.toList else [])

/-- `"ZTxAuthHash_" || CONSENSUS_BRANCH_ID`. -/
def authPersonalization (branchId : BitVec 32) : Personalization :=
  ⟨(ascii "ZTxAuthHash_" 12).toList ++ u32 branchId, by simp [ascii, u32, I2LEOSP]⟩

/-! ## Transactions -/

/-- The Orchard digest (§T.4; ZIP 229). -/
def Transaction.orchardDigest (tx : Transaction) : Digest :=
  if tx.format.IsV6 then actionsDigest H orchardV6 true tx.orchard
  else actionsDigest H orchardV5 false tx.orchard

/-- The format with its Ironwood digest. -/
def Transaction.version (tx : Transaction) : Version :=
  match tx.format with
  | .v5 => .v5
  | .v6 ironwood => .v6 (actionsDigest H ironwoodV6 true ironwood)

/-- The transaction identifier digest (§T; ZIP 229). -/
def Transaction.txid (tx : Transaction) : Digest :=
  txidDigest H tx.transparent (tx.version H) tx.header.consensusBranchId (headerDigest H tx.header)
    (saplingDigest H tx.format tx.sapling) (tx.orchardDigest H)

/-- The signature digest of `input` (§S; ZIP 229). -/
def Transaction.signatureDigest (tx : Transaction) (input : SignableInput tx.transparent) :
    Digest :=
  Spec.signatureDigest H (tx.version H) tx.header.consensusBranchId (headerDigest H tx.header)
    (saplingDigest H tx.format tx.sapling) (tx.orchardDigest H) input

/-- The authorizing data commitment (§A); for version 6, ZIP 229 (the Ironwood auth digest
    last). -/
def Transaction.authDigest (tx : Transaction) : Digest :=
  node H (authPersonalization tx.header.consensusBranchId)
    ([transparentScriptsDigest H tx.scriptSigs, saplingAuthDigest H tx.format tx.sapling,
        if tx.format.IsV6 then actionsAuthDigest H orchardV6 true tx.orchard
        else actionsAuthDigest H orchardV5 false tx.orchard] ++
      match tx.format with
      | .v5 => []
      | .v6 ironwood => [actionsAuthDigest H ironwoodV6 true ironwood])

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
