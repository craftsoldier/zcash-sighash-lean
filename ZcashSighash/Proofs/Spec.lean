/-
What the specification is meant to do, checked against what it says: ZIP 244's requirements and
rationale, stated as theorems about `Spec`.
-/
module

public import ZcashSighash.Spec

@[expose] public section

namespace ZcashSighash.Spec

/-- §S.2a: a hash type's byte encodes it. -/
theorem HashType.ofByte?_toByte (h : HashType) : HashType.ofByte? h.toByte = some h := by
  obtain ⟨base, acp⟩ := h
  cases base <;> cases acp <;> decide

/-- §S.2a: the six bytes that encode hash types are exactly their encodings. -/
theorem HashType.toByte_of_ofByte? (b : Byte) (h : HashType) (hb : HashType.ofByte? b = some h) :
    h.toByte = b := by
  revert h
  revert b
  decide

/-- A `uint32`'s four bytes determine it. `signatureDigest_all_commits` uses this to read back
    prevout indices and sequence numbers. -/
theorem u32_injective : Function.Injective u32 := by
  intro a b h
  simp [u32, I2LEOSP, List.range_succ] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at e0 e1 e2 e3
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  omega

/-- An `int64`'s eight bytes determine it. `signatureDigest_all_commits` uses this to read back
    the spent values and output values. -/
theorem i64_injective : Function.Injective i64 := by
  intro a b h
  simp [i64, I2LEOSP, List.range_succ, BitVec.toNat_eq] at h
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  omega

/-- `compactSize` is prefix-free and injective. -/
theorem compactSize_append_inj {a b : BitVec 64} {x y : List Byte}
    (h : compactSize a ++ x = compactSize b ++ y) : a = b ∧ x = y := by
  have ha := a.isLt
  have hb := b.isLt
  unfold compactSize at h
  split_ifs at h <;> simp [I2LEOSP, List.range_succ, BitVec.toNat_eq] at h <;>
    first | (exfalso; omega) | exact ⟨BitVec.eq_of_toNat_eq (by omega), by tauto⟩

/-- A script's length, as `script` encodes it, is its length below `2 ^ 64`. -/
theorem ofNat_length_inj {s s' : List Byte} (h : s.length < 2 ^ 64) (h' : s'.length < 2 ^ 64)
    (hl : BitVec.ofNat 64 s.length = BitVec.ofNat 64 s'.length) : s.length = s'.length := by
  have := congrArg BitVec.toNat hl
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- Unique decoding of §S.2d: concatenated script field encodings determine the scripts. -/
theorem script_flatMap_injective (ss₁ ss₂ : List (List Byte))
    (h₁ : ∀ s ∈ ss₁, s.length < 2 ^ 64) (h₂ : ∀ s ∈ ss₂, s.length < 2 ^ 64)
    (h : ss₁.flatMap script = ss₂.flatMap script) : ss₁ = ss₂ := by
  induction ss₁ generalizing ss₂ with
  | nil =>
    cases ss₂ with
    | nil => rfl
    | cons s ss => simp [script, compactSize, I2LEOSP] at h; split_ifs at h <;> simp at h
  | cons s ss ih =>
    cases ss₂ with
    | nil => simp [script, compactSize, I2LEOSP] at h; split_ifs at h <;> simp at h
    | cons s' ss' =>
      simp only [List.flatMap_cons, script, List.append_assoc] at h
      obtain ⟨hl, hrest⟩ := compactSize_append_inj h
      obtain ⟨hs, htl⟩ :=
        List.append_inj hrest (ofNat_length_inj (h₁ s (by simp)) (h₂ s' (by simp)) hl)
      subst hs
      rw [ih ss' (fun t ht => h₁ t (by simp [ht])) (fun t ht => h₂ t (by simp [ht])) htl]

/-- Unique decoding of §T.2c: concatenated output field encodings determine the outputs. -/
theorem TxOut.encode_flatMap_injective (os₁ os₂ : List TxOut)
    (h₁ : ∀ o ∈ os₁, o.scriptPubKey.length < 2 ^ 64)
    (h₂ : ∀ o ∈ os₂, o.scriptPubKey.length < 2 ^ 64)
    (h : os₁.flatMap TxOut.encode = os₂.flatMap TxOut.encode) : os₁ = os₂ := by
  induction os₁ generalizing os₂ with
  | nil => cases os₂ with
    | nil => rfl
    | cons o os => simp [TxOut.encode, i64, I2LEOSP] at h
  | cons o os ih =>
    cases os₂ with
    | nil => simp [TxOut.encode, i64, I2LEOSP] at h
    | cons o' os' =>
      simp only [List.flatMap_cons, TxOut.encode, script, List.append_assoc] at h
      obtain ⟨hv, hrest⟩ := List.append_inj h (by simp [i64, I2LEOSP])
      obtain ⟨hl, hrest⟩ := compactSize_append_inj hrest
      obtain ⟨hs, htl⟩ :=
        List.append_inj hrest (ofNat_length_inj (h₁ o (by simp)) (h₂ o' (by simp)) hl)
      have := ih os' (fun t ht => h₁ t (by simp [ht])) (fun t ht => h₂ t (by simp [ht])) htl
      obtain ⟨v, s⟩ := o
      obtain ⟨v', s'⟩ := o'
      simp_all [i64_injective.eq_iff]

/-- An outpoint's field encoding determines the outpoint. -/
theorem OutPoint.encode_injective : Function.Injective OutPoint.encode := by
  intro ⟨h₁, n₁⟩ ⟨h₂, n₂⟩ h
  obtain ⟨hh, hn⟩ := List.append_inj h (by simp)
  simp only [OutPoint.mk.injEq]
  exact ⟨List.Vector.toList_injective hh, u32_injective hn⟩

/-! ## Collision-freedom on the inputs a digest hashes

No hash has no collisions at all: it maps infinitely many inputs to `2 ^ 256` digests. The
theorems that a digest commits to its data assume only that the hash has no collision among a
finite list of inputs built from the two transactions: the inputs computing their digests feeds
it, and for simplicity a few it would feed in the other format or with an empty component. So a
counterexample to them is a collision among inputs determined by the two transactions. -/

/-- `H` has no collision among the inputs `S`: two of them with one digest are the same. -/
def CollisionFreeOn (H : Hash) (S : List (Personalization × List Byte)) : Prop :=
  ∀ p₁ x₁ p₂ x₂, (p₁, x₁) ∈ S → (p₂, x₂) ∈ S → H p₁ x₁ = H p₂ x₂ → p₁ = p₂ ∧ x₁ = x₂

/-- Two inputs under one personalization with one digest are the same. -/
theorem CollisionFreeOn.eq {H : Hash} {S : List (Personalization × List Byte)}
    (hH : CollisionFreeOn H S) {p : Personalization} {x y : List Byte} (hx : (p, x) ∈ S)
    (hy : (p, y) ∈ S) (h : H p x = H p y) : x = y :=
  (hH _ _ _ _ hx hy h).2

section
variable (H : Hash)

/-- The input §S's root hashes. -/
def signatureInput (v : Version) (branchId : BitVec 32) (header sapling orchard : Digest)
    {t : Transparent} (input : SignableInput t) : Personalization × List Byte :=
  (txHashPersonalization branchId, ([header, transparentSigDigest H input, sapling, orchard] ++
    match v with | .v5 => [] | .v6 ironwood => [ironwood]).flatMap (·.toList))

/-- The input §T's root hashes. -/
def txidInput (t : Transparent) (v : Version) (branchId : BitVec 32)
    (header sapling orchard : Digest) : Personalization × List Byte :=
  (txHashPersonalization branchId, ([header, transparentDigest H t, sapling, orchard] ++
    match v with | .v5 => [] | .v6 ironwood => [ironwood]).flatMap (·.toList))

/-- The input §S.2 hashes outside coinbase transactions. -/
def transparentSigInput {t : Transparent} (input : SignableInput t) :
    Personalization × List Byte :=
  (personal "ZTxIdTranspaHash", input.hashType.toByte ::
    [prevoutsSigDigest H t input.hashType, amountsSigDigest H t input.hashType,
      scriptPubKeysSigDigest H t input.hashType, sequenceSigDigest H t input.hashType,
      outputsSigDigest H input, txinSigDigest H input].flatMap (·.toList))

/-- The input §S.2g hashes for the transparent input `i`. -/
def txinInput (t : Transparent) (i : Fin t.vin.length) : Personalization × List Byte :=
  (personal "Zcash___TxInHash", t.vin[i].prevout.encode ++ i64 t.vin[i].spent.value ++
    script t.vin[i].spent.scriptPubKey ++ u32 t.vin[i].nSequence)

/-- > for fully shielded transactions, `signature_digest` is equal to `txid_digest`
    (ZIP 244, Rationale); likewise for a coinbase transaction, and for any input. -/
theorem signatureDigest_eq_txidDigest (t : Transparent) (hcb : t.IsCoinbase ∨ t.vin = [])
    (v : Version) (branchId : BitVec 32) (header sapling orchard : Digest)
    (input : SignableInput t) :
    signatureDigest H v branchId header sapling orchard input =
      txidDigest H t v branchId header sapling orchard := by
  simp [signatureDigest, txidDigest, transparentSigDigest, hcb]

/-- `SIGHASH_NONE`: the signature commits to no outputs, unless the transaction is a coinbase
    transaction, whose digest is §T.2's for every input. -/
theorem transparentSigDigest_none (vin : List TxIn) (vout₁ vout₂ : List TxOut) (acp : Bool)
    (hcb : ¬(⟨vin, vout₁⟩ : Transparent).IsCoinbase) (i : Fin vin.length) :
    transparentSigDigest H (t := ⟨vin, vout₁⟩) (.transparent ⟨.none, acp⟩ i) =
      transparentSigDigest H (t := ⟨vin, vout₂⟩) (.transparent ⟨.none, acp⟩ i) := by
  have hvin : vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  simp only [Transparent.IsCoinbase] at hcb
  simp [transparentSigDigest, prevoutsSigDigest, prevoutsDigest, amountsSigDigest, hcb, hvin,
    scriptPubKeysSigDigest, sequenceSigDigest, sequenceDigest, outputsSigDigest, txinSigDigest,
    Transparent.IsCoinbase, SignableInput.hashType]
  rfl

/-- `SIGHASH_ANYONECANPAY`: the signature commits to its own input, not to the other inputs nor to
    its index, outside coinbase transactions. -/
theorem transparentSigDigest_anyoneCanPay (vin₁ vin₂ : List TxIn) (vout : List TxOut)
    (base : Base) (hb : base ≠ .single)
    (hcb₁ : ¬(⟨vin₁, vout⟩ : Transparent).IsCoinbase)
    (hcb₂ : ¬(⟨vin₂, vout⟩ : Transparent).IsCoinbase)
    (i : Fin vin₁.length) (j : Fin vin₂.length) (hij : vin₁[i] = vin₂[j]) :
    transparentSigDigest H (t := ⟨vin₁, vout⟩) (.transparent ⟨base, true⟩ i) =
      transparentSigDigest H (t := ⟨vin₂, vout⟩) (.transparent ⟨base, true⟩ j) := by
  have hvin₁ : vin₁ ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hvin₂ : vin₂ ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)
  have h₁ : ¬((⟨vin₁, vout⟩ : Transparent).IsCoinbase ∨ vin₁ = []) := by simp [hcb₁, hvin₁]
  have h₂ : ¬((⟨vin₂, vout⟩ : Transparent).IsCoinbase ∨ vin₂ = []) := by simp [hcb₂, hvin₂]
  simp only [Fin.getElem_fin] at hij
  rw [transparentSigDigest, transparentSigDigest, ite_eq_right h₁, ite_eq_right h₂]
  cases base <;> simp_all [prevoutsSigDigest, amountsSigDigest, scriptPubKeysSigDigest,
    sequenceSigDigest, outputsSigDigest, outputsDigest, txinSigDigest, SignableInput.hashType]

/-- `SIGHASH_SINGLE | SIGHASH_ANYONECANPAY`: the signature commits to its own input and the output
    at its index, not to the index itself, so input-output pairs can move together (ZIP 143). -/
theorem transparentSigDigest_single_anyoneCanPay (t₁ t₂ : Transparent)
    (hcb₁ : ¬t₁.IsCoinbase) (hcb₂ : ¬t₂.IsCoinbase)
    (i : Fin t₁.vin.length) (j : Fin t₂.vin.length) (hij : t₁.vin[i] = t₂.vin[j])
    (hout : t₁.vout[i.val]? = t₂.vout[j.val]?) :
    transparentSigDigest H (.transparent ⟨.single, true⟩ i) =
      transparentSigDigest H (.transparent ⟨.single, true⟩ j) := by
  have hvin₁ : t₁.vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hvin₂ : t₂.vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt)
  simp only [Fin.getElem_fin] at hij
  simp [transparentSigDigest, prevoutsSigDigest, amountsSigDigest, scriptPubKeysSigDigest,
    sequenceSigDigest, outputsSigDigest, txinSigDigest, SignableInput.hashType, hcb₁, hcb₂, hvin₁,
    hvin₂, hij, hout]

/-- A signature digest names its input by content, not position: two inputs with the same
    contents (and, for `SIGHASH_SINGLE`, the same output at their index) share it. Only the
    consensus rule against two inputs spending one output separates them. -/
theorem transparentSigDigest_eq_of_txin_eq (t : Transparent) (h : HashType)
    (i j : Fin t.vin.length) (hij : t.vin[i] = t.vin[j])
    (hout : h.base = .single → t.vout[i.val]? = t.vout[j.val]?) :
    transparentSigDigest H (.transparent h i) = transparentSigDigest H (.transparent h j) := by
  obtain ⟨base, acp⟩ := h
  simp only [Fin.getElem_fin] at hij
  cases base <;>
    simp_all [transparentSigDigest, outputsSigDigest, txinSigDigest, SignableInput.hashType]

/-- `SIGHASH_SINGLE` without a corresponding output commits to no outputs, as `SIGHASH_NONE` does
    ("silently misleading", ZIP 244, Rationale); outside coinbase transactions. -/
theorem transparentSigDigest_single_no_output (vin : List TxIn) (vout₁ vout₂ : List TxOut)
    (acp : Bool) (hcb : ¬(⟨vin, vout₁⟩ : Transparent).IsCoinbase) (i : Fin vin.length)
    (h₁ : vout₁.length ≤ i.val) (h₂ : vout₂.length ≤ i.val) :
    transparentSigDigest H (t := ⟨vin, vout₁⟩) (.transparent ⟨.single, acp⟩ i) =
      transparentSigDigest H (t := ⟨vin, vout₂⟩) (.transparent ⟨.single, acp⟩ i) := by
  have hvin : vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  simp only [Transparent.IsCoinbase] at hcb
  simp [transparentSigDigest, prevoutsSigDigest, prevoutsDigest, amountsSigDigest, hcb, hvin,
    scriptPubKeysSigDigest, sequenceSigDigest, sequenceDigest, outputsSigDigest, txinSigDigest,
    Transparent.IsCoinbase, SignableInput.hashType, List.getElem?_eq_none h₁,
    List.getElem?_eq_none h₂]
  rfl

/-- Different hash types have different bytes, so §S.2a's first byte commits to the hash
    type. -/
theorem HashType.toByte_injective : Function.Injective HashType.toByte := by
  intro a b h
  simpa [HashType.ofByte?_toByte] using congrArg HashType.ofByte? h

/-- Different hash types give different preimages, outside coinbase transactions (their first
    bytes differ), so equal digests are a collision of these two inputs. -/
theorem transparentSigDigest_ne_of_hashType_ne (t : Transparent) (hcb : ¬t.IsCoinbase)
    (h₁ h₂ : HashType) (hne : h₁ ≠ h₂) (i : Fin t.vin.length)
    (hH : CollisionFreeOn H [transparentSigInput H (.transparent h₁ i),
      transparentSigInput H (.transparent h₂ i)]) :
    transparentSigDigest H (.transparent h₁ i) ≠ transparentSigDigest H (.transparent h₂ i) := by
  intro heq
  have hvin : t.vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hc : ¬(t.IsCoinbase ∨ t.vin = []) := by simp [hcb, hvin]
  rw [transparentSigDigest, transparentSigDigest, ite_eq_right hc, ite_eq_right hc] at heq
  exact hne (HashType.toByte_injective (List.cons.inj
    (hH.eq List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) heq)).1)

/-- A transparent signature digest is never the transaction's identifier, outside coinbase
    transactions, unless their preimages collide. -/
theorem signatureDigest_ne_txidDigest (t : Transparent) (hcb : ¬t.IsCoinbase) (v : Version)
    (branchId : BitVec 32) (header sapling orchard : Digest) (h : HashType)
    (i : Fin t.vin.length)
    (hH : CollisionFreeOn H [signatureInput H v branchId header sapling orchard (.transparent h i),
      txidInput H t v branchId header sapling orchard, transparentSigInput H (.transparent h i),
      (personal "ZTxIdTranspaHash",
        [prevoutsDigest H t, sequenceDigest H t, outputsDigest H t].flatMap (·.toList))]) :
    signatureDigest H v branchId header sapling orchard (.transparent h i) ≠
      txidDigest H t v branchId header sapling orchard := by
  intro heq
  have hvin : t.vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hc : ¬(t.IsCoinbase ∨ t.vin = []) := by simp [hcb, hvin]
  have hpre := hH.eq List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) heq
  simp only [List.cons_append, List.flatMap_cons, List.append_cancel_left_eq] at hpre
  have hd := List.Vector.toList_injective (List.append_inj hpre (by simp)).1
  have he : t.vin.isEmpty = false := by simpa using hvin
  rw [transparentSigDigest, ite_eq_right hc, transparentDigest] at hd
  simp only [he, Bool.false_and, Bool.false_eq_true, ite_false, node] at hd
  simpa using congrArg List.length
    (hH.eq (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      hd)

/-- Version 5 and version 6 signature digests have different preimages under one branch ID,
    whatever their headers, transactions and inputs: the root's personalization is shared, and
    only the preimage's length (4 against 5 digests) separates them. So equal digests are a
    collision of these two inputs. -/
theorem signatureDigest_v5_ne_v6 (t₁ t₂ : Transparent) (branchId : BitVec 32)
    (header₁ sapling₁ orchard₁ : Digest) (header₂ sapling₂ orchard₂ ironwood : Digest)
    (input₁ : SignableInput t₁) (input₂ : SignableInput t₂)
    (hH : CollisionFreeOn H [signatureInput H .v5 branchId header₁ sapling₁ orchard₁ input₁,
      signatureInput H (.v6 ironwood) branchId header₂ sapling₂ orchard₂ input₂]) :
    signatureDigest H .v5 branchId header₁ sapling₁ orchard₁ input₁ ≠
      signatureDigest H (.v6 ironwood) branchId header₂ sapling₂ orchard₂ input₂ := by
  intro heq
  simpa using congrArg List.length
    (hH.eq List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) heq)

/-- Likewise for the transaction identifiers: their preimages differ in length. -/
theorem txidDigest_v5_ne_v6 (t₁ t₂ : Transparent) (branchId : BitVec 32)
    (header₁ sapling₁ orchard₁ : Digest) (header₂ sapling₂ orchard₂ ironwood : Digest)
    (hH : CollisionFreeOn H [txidInput H t₁ .v5 branchId header₁ sapling₁ orchard₁,
      txidInput H t₂ (.v6 ironwood) branchId header₂ sapling₂ orchard₂]) :
    txidDigest H t₁ .v5 branchId header₁ sapling₁ orchard₁ ≠
      txidDigest H t₂ (.v6 ironwood) branchId header₂ sapling₂ orchard₂ := by
  intro heq
  simpa using congrArg List.length
    (hH.eq List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) heq)

/-- Inputs spending different outputs have different digests, unless their preimages collide. -/
theorem transparentSigDigest_ne_of_prevout_ne (t : Transparent) (hcb : ¬t.IsCoinbase)
    (h : HashType) (i j : Fin t.vin.length) (hp : t.vin[i].prevout ≠ t.vin[j].prevout)
    (hH : CollisionFreeOn H [transparentSigInput H (.transparent h i),
      transparentSigInput H (.transparent h j), txinInput t i, txinInput t j]) :
    transparentSigDigest H (.transparent h i) ≠ transparentSigDigest H (.transparent h j) := by
  intro heq
  have hvin : t.vin ≠ [] := List.ne_nil_of_length_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  have hc : ¬(t.IsCoinbase ∨ t.vin = []) := by simp [hcb, hvin]
  rw [transparentSigDigest, transparentSigDigest, ite_eq_right hc, ite_eq_right hc] at heq
  have hpre := hH.eq List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) heq
  simp only [List.cons.injEq, true_and, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_cancel_left_eq, SignableInput.hashType] at hpre
  obtain ⟨-, htxin⟩ := List.append_inj hpre (by simp)
  have hv := List.Vector.toList_injective htxin
  simp only [txinSigDigest] at hv
  have htxin' := hH.eq (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    hv
  simp only [List.append_assoc] at htxin'
  exact hp (OutPoint.encode_injective (List.append_inj htxin' (by simp [OutPoint.encode, u32,
    I2LEOSP])).1)

end

/-! ## What a `SIGHASH_ALL` signature commits to -/

/-- Concatenating a fixed-length injective encoding is injective. -/
theorem flatMap_injective_of_length {α : Type} (f : α → List Byte) (k : ℕ) (hk : 0 < k)
    (hl : ∀ a, (f a).length = k) (hf : Function.Injective f) :
    Function.Injective (fun l : List α => l.flatMap f) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons a l => have := congrArg List.length h; simp [hl] at this; omega
  | cons a l ih =>
    intro l₂ h
    cases l₂ with
    | nil => have := congrArg List.length h; simp [hl] at this; omega
    | cons a' l' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨ha, hrest⟩ := List.append_inj h (by simp [hl])
      rw [hf ha, ih hrest]

/-- A node's digest determines its children, unless its two inputs collide. -/
theorem node_eq {H : Hash} {S : List (Personalization × List Byte)} (hH : CollisionFreeOn H S)
    {p : Personalization} {ds es : List Digest} (hd : (p, ds.flatMap (·.toList)) ∈ S)
    (he : (p, es.flatMap (·.toList)) ∈ S) (h : node H p ds = node H p es) : ds = es :=
  flatMap_injective_of_length List.Vector.toList 32 (by decide) (by simp)
    List.Vector.toList_injective (hH.eq hd he h)

/-- A `uint32` encodes to 4 bytes, so a run of them splits back into its values. -/
theorem u32_length (x : BitVec 32) : (u32 x).length = 4 := by simp [u32, I2LEOSP]

/-- An `int64` encodes to 8 bytes, so a run of them splits back into its values. -/
theorem i64_length (x : BitVec 64) : (i64 x).length = 8 := by simp [i64, I2LEOSP]

/-- An outpoint encodes to 36 bytes (a 32-byte hash and a 4-byte index), so §T.2a's preimage
    splits back into its outpoints. -/
theorem OutPoint.encode_length (o : OutPoint) : o.encode.length = 36 := by
  simp [OutPoint.encode, u32, I2LEOSP]

/-- Inputs with the same prevout, sequence number, spent value and spent script are equal. -/
theorem TxIn.ext' (a b : TxIn) (hp : a.prevout = b.prevout) (hs : a.nSequence = b.nSequence)
    (hv : a.spent.value = b.spent.value) (hk : a.spent.scriptPubKey = b.spent.scriptPubKey) :
    a = b := by
  obtain ⟨_, _, ⟨_, _⟩⟩ := a
  obtain ⟨_, _, ⟨_, _⟩⟩ := b
  simp_all

/-- Transparent parts with the same inputs and outputs are equal. -/
theorem Transparent.ext' {a b : Transparent} (hi : a.vin = b.vin) (ho : a.vout = b.vout) :
    a = b := by
  cases a
  cases b
  simp_all

/-- Inputs are equal when their prevouts, sequences, spent values and spent scripts are. -/
theorem TxIn.list_ext {l₁ l₂ : List TxIn} (hp : l₁.map (·.prevout) = l₂.map (·.prevout))
    (hs : l₁.map (·.nSequence) = l₂.map (·.nSequence))
    (hv : l₁.map (·.spent.value) = l₂.map (·.spent.value))
    (hk : l₁.map (·.spent.scriptPubKey) = l₂.map (·.spent.scriptPubKey)) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simpa using hp.symm
  | cons a l ih =>
    cases l₂ with
    | nil => simp at hp
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at hp hs hv hk
      rw [ih hp.2 hs.2 hv.2 hk.2]
      obtain ⟨_, _, _, _⟩ := a
      obtain ⟨_, _, _, _⟩ := b
      simp_all

section
variable (H : Hash)

/-- The inputs a `SIGHASH_ALL` signature digest of the input `i` hashes, outside coinbase
    transactions. -/
def sigAllInputs (v : Version) (branchId : BitVec 32) (header sapling orchard : Digest)
    (t : Transparent) (i : Fin t.vin.length) : List (Personalization × List Byte) :=
  [signatureInput H v branchId header sapling orchard (.transparent ⟨.all, false⟩ i),
    transparentSigInput H (.transparent ⟨.all, false⟩ i),
    (personal "ZTxIdPrevoutHash", t.vin.flatMap (·.prevout.encode)),
    (personal "ZTxTrAmountsHash", t.vin.flatMap (i64 ·.spent.value)),
    (personal "ZTxTrScriptsHash", t.vin.flatMap (script ·.spent.scriptPubKey)),
    (personal "ZTxIdSequencHash", t.vin.flatMap (u32 ·.nSequence)),
    (personal "ZTxIdOutputsHash", t.vout.flatMap TxOut.encode), txinInput t i]

/-- `SIGHASH_ALL` commits to the whole transparent part: outside coinbase transactions, equal
    signature digests mean equal transparent parts, inputs of equal contents, and equal header,
    Sapling and Orchard digests, unless computing the digests finds a hash collision. -/
theorem signatureDigest_all_commits (t₁ t₂ : Transparent)
    (hcb₁ : ¬t₁.IsCoinbase) (hcb₂ : ¬t₂.IsCoinbase)
    (hk₁ : ∀ x ∈ t₁.vin, x.spent.scriptPubKey.length < 2 ^ 64)
    (hk₂ : ∀ x ∈ t₂.vin, x.spent.scriptPubKey.length < 2 ^ 64)
    (ho₁ : ∀ o ∈ t₁.vout, o.scriptPubKey.length < 2 ^ 64)
    (ho₂ : ∀ o ∈ t₂.vout, o.scriptPubKey.length < 2 ^ 64)
    (v : Version) (branchId : BitVec 32) (header₁ sapling₁ orchard₁ : Digest)
    (header₂ sapling₂ orchard₂ : Digest) (i : Fin t₁.vin.length) (j : Fin t₂.vin.length)
    (hH : CollisionFreeOn H (sigAllInputs H v branchId header₁ sapling₁ orchard₁ t₁ i ++
      sigAllInputs H v branchId header₂ sapling₂ orchard₂ t₂ j))
    (heq : signatureDigest H v branchId header₁ sapling₁ orchard₁
        (.transparent ⟨.all, false⟩ i) =
      signatureDigest H v branchId header₂ sapling₂ orchard₂ (.transparent ⟨.all, false⟩ j)) :
    t₁ = t₂ ∧ t₁.vin[i] = t₂.vin[j] ∧ header₁ = header₂ ∧ sapling₁ = sapling₂ ∧
      orchard₁ = orchard₂ := by
  -- The `k`th input each side hashes.
  have m₁ : ∀ k (hk : k < 8), (sigAllInputs H v branchId header₁ sapling₁ orchard₁ t₁ i)[k] ∈
      sigAllInputs H v branchId header₁ sapling₁ orchard₁ t₁ i ++
        sigAllInputs H v branchId header₂ sapling₂ orchard₂ t₂ j :=
    fun k hk => List.mem_append_left _ (List.getElem_mem _)
  have m₂ : ∀ k (hk : k < 8), (sigAllInputs H v branchId header₂ sapling₂ orchard₂ t₂ j)[k] ∈
      sigAllInputs H v branchId header₁ sapling₁ orchard₁ t₁ i ++
        sigAllInputs H v branchId header₂ sapling₂ orchard₂ t₂ j :=
    fun k hk => List.mem_append_right _ (List.getElem_mem _)
  have hc := flatMap_injective_of_length List.Vector.toList 32 (by decide) (by simp)
    List.Vector.toList_injective (hH.eq (m₁ 0 (by decide)) (m₂ 0 (by decide)) heq)
  simp only [List.cons_append, List.cons.injEq] at hc
  obtain ⟨hh, ht, hs, ho, -⟩ := hc
  have hvin₁ : t₁.vin ≠ [] := List.ne_nil_of_length_pos (by have := i.isLt; omega)
  have hvin₂ : t₂.vin ≠ [] := List.ne_nil_of_length_pos (by have := j.isLt; omega)
  have hne₁ : ¬(t₁.IsCoinbase ∨ t₁.vin = []) := by simp [hcb₁, hvin₁]
  have hne₂ : ¬(t₂.IsCoinbase ∨ t₂.vin = []) := by simp [hcb₂, hvin₂]
  rw [transparentSigDigest, transparentSigDigest, ite_eq_right hne₁, ite_eq_right hne₂] at ht
  have h6 := flatMap_injective_of_length List.Vector.toList 32 (by decide) (by simp)
    List.Vector.toList_injective
      (List.cons.inj (hH.eq (m₁ 1 (by decide)) (m₂ 1 (by decide)) ht)).2
  simp only [List.cons.injEq, SignableInput.hashType, prevoutsSigDigest, amountsSigDigest,
    scriptPubKeysSigDigest, sequenceSigDigest, outputsSigDigest, txinSigDigest, prevoutsDigest,
    sequenceDigest, outputsDigest, Bool.false_eq_true, ite_false, and_true] at h6
  obtain ⟨hp, ha, hk, hq, hout, htx⟩ := h6
  have hp := hH.eq (m₁ 2 (by decide)) (m₂ 2 (by decide)) hp
  have ha := hH.eq (m₁ 3 (by decide)) (m₂ 3 (by decide)) ha
  have hk := hH.eq (m₁ 4 (by decide)) (m₂ 4 (by decide)) hk
  have hq := hH.eq (m₁ 5 (by decide)) (m₂ 5 (by decide)) hq
  have hout := hH.eq (m₁ 6 (by decide)) (m₂ 6 (by decide)) hout
  have hpre := hH.eq (m₁ 7 (by decide)) (m₂ 7 (by decide)) htx
  -- §T.2a, §T.2b, §S.2c, §S.2d: the per-input lists.
  have hp' : t₁.vin.map (·.prevout) = t₂.vin.map (·.prevout) :=
    flatMap_injective_of_length OutPoint.encode 36 (by decide) OutPoint.encode_length
      OutPoint.encode_injective (by simpa [List.flatMap_map] using hp)
  have hq' : t₁.vin.map (·.nSequence) = t₂.vin.map (·.nSequence) :=
    flatMap_injective_of_length u32 4 (by decide) u32_length u32_injective
      (by simpa [List.flatMap_map] using hq)
  have ha' : t₁.vin.map (·.spent.value) = t₂.vin.map (·.spent.value) :=
    flatMap_injective_of_length i64 8 (by decide) i64_length i64_injective
      (by simpa [List.flatMap_map] using ha)
  have hk' : t₁.vin.map (·.spent.scriptPubKey) = t₂.vin.map (·.spent.scriptPubKey) :=
    script_flatMap_injective _ _ (by simpa using hk₁) (by simpa using hk₂)
      (by simpa [List.flatMap_map] using hk)
  -- §T.2c: the outputs.
  have hout' : t₁.vout = t₂.vout := TxOut.encode_flatMap_injective _ _ ho₁ ho₂ hout
  -- §S.2g: the input's own fields.
  simp only [List.append_assoc] at hpre
  obtain ⟨hpo, r⟩ := List.append_inj hpre (by simp [OutPoint.encode_length])
  obtain ⟨hva, r⟩ := List.append_inj r (by simp [i64_length])
  simp only [script, List.append_assoc] at r
  obtain ⟨hl, r⟩ := compactSize_append_inj r
  obtain ⟨hsc, hse⟩ := List.append_inj r
    (ofNat_length_inj (hk₁ _ (List.getElem_mem _)) (hk₂ _ (List.getElem_mem _)) hl)
  have hin : t₁.vin[i] = t₂.vin[j] :=
    TxIn.ext' _ _ (OutPoint.encode_injective hpo) (u32_injective hse) (i64_injective hva) hsc
  exact ⟨Transparent.ext' (TxIn.list_ext hp' hq' ha' hk') hout', hin, hh, hs, ho⟩

end

-- The build fails if the theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Spec.signatureDigest_all_commits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signatureDigest_all_commits

end ZcashSighash.Spec
