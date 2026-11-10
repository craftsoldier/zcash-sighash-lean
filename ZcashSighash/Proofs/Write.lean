/-
What `zcash_primitives`' writer does with what its reader returns: a version 5 or 6 transaction
`Transaction::read` returns is written back as exactly the bytes it was read from
(`write_eq_read_bytes`), so reading what was written gives the same transaction back
(`write_read`). In version 6 with an Orchard or Ironwood bundle this needs a consensus branch ID
of NU6.3 or NU7, under which the bundle versions are the ones `write_v6_bundle` accepts; under
NU5 to NU6.2, writing a transaction with an Orchard bundle fails (`write_v6_earlier`).
-/
module

public import ZcashSighash.Proofs.Read
public import ZcashSighash.Proofs.VerifierV4
public import ZcashSighash.Verifier.Write

@[expose] public section

namespace ZcashSighash.Verifier.Read

open Spec (Byte Bytes)
open Native (Parser readBytes readLe fail readCount Parser.bind_eq_some pure_apply)

/-! ## Reading consumes a prefix -/

/-- A parser that, where it succeeds, reads a prefix of its input, and reads that prefix the
    same way before anything else. -/
def Consumes {α : Type} (p : Parser α) : Prop :=
  ∀ s a s', p s = some (a, s') → ∃ w, s = w ++ s' ∧ ∀ r, p (w ++ r) = some (a, r)

/-- A value returned reads nothing. -/
theorem consumes_pure {α : Type} (a : α) : Consumes (pure a : Parser α) := by
  intro s b s' h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨[], rfl, fun r => rfl⟩

/-- An error reads nothing it returns. -/
theorem consumes_fail {α : Type} : Consumes (fail : Parser α) := by
  intro s a s' h
  simp at h

/-- Two reads in turn read what each reads, in turn. -/
theorem consumes_bind {α β : Type} {p : Parser α} {f : α → Parser β} (hp : Consumes p)
    (hf : ∀ a, Consumes (f a)) : Consumes (p >>= f) := by
  intro s b s' h
  obtain ⟨a, s₁, h₁, h₂⟩ := Parser.bind_eq_some.mp h
  obtain ⟨w₁, rfl, hw₁⟩ := hp s a s₁ h₁
  obtain ⟨w₂, rfl, hw₂⟩ := hf a s₁ b s' h₂
  refine ⟨w₁ ++ w₂, by simp, fun r => Parser.bind_eq_some.mpr ⟨a, w₂ ++ r, ?_, hw₂ r⟩⟩
  simpa using hw₁ (w₂ ++ r)

/-- `read_exact` reads the bytes it returns. -/
theorem consumes_readBytes (n : ℕ) : Consumes (readBytes n) := by
  intro s b s' h
  unfold readBytes at h
  split_ifs at h with hn
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨s.take n, by simp, fun r => ?_⟩
  have hl : (s.take n).length = n := by simp; omega
  simp [readBytes, hl]

/-- A loop of reads that consume their input consumes its input. -/
theorem consumes_readCount {α : Type} {p : Parser α} (hp : Consumes p) :
    ∀ n, Consumes (readCount p n)
  | 0 => consumes_pure []
  | n + 1 => consumes_bind hp fun _ => consumes_bind (consumes_readCount hp n) fun _ =>
      consumes_pure _

/-- A read whose value is mapped reads what the read does. -/
theorem consumes_map {α β : Type} (f : α → β) {p : Parser α} (hp : Consumes p) :
    Consumes (f <$> p) := by
  intro s b s' h
  cases hs : p s with
  | none => simp [Functor.map, StateT.map, hs] at h
  | some r =>
    obtain ⟨a, s₁⟩ := r
    simp only [Functor.map, StateT.map, hs, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, rfl, hw⟩ := hp _ a _ hs
    exact ⟨w, rfl, fun r => by simp [Functor.map, StateT.map, hw r]⟩

/-! ## Little-endian integers -/

/-- The little-endian value of bytes, as `readLe` computes it. -/
def leValue (b : List Byte) : ℕ := b.foldr (fun c acc => c.toNat + 256 * acc) 0

/-- The little-endian value of `n` bytes is less than `256 ^ n`. -/
theorem leValue_lt (b : List Byte) : leValue b < 256 ^ b.length := by
  induction b with
  | nil => simp [leValue]
  | cons c b ih =>
    simp only [leValue, List.foldr_cons, List.length_cons, pow_succ] at ih ⊢
    have := c.isLt
    omega

/-- The bytes of the little-endian value of bytes are those bytes. -/
theorem leValue_bytes (b : List Byte) :
    (List.range b.length).map (fun j => BitVec.ofNat 8 (leValue b / 256 ^ j)) = b := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have hc := c.isLt
    have h0 : BitVec.ofNat 8 (leValue (c :: b) / 256 ^ 0) = c := by
      apply BitVec.eq_of_toNat_eq
      simp only [leValue, List.foldr_cons, pow_zero, Nat.div_one, BitVec.toNat_ofNat]
      omega
    have hs : ((fun j => BitVec.ofNat 8 (leValue (c :: b) / 256 ^ j)) ∘ Nat.succ) =
        fun j => BitVec.ofNat 8 (leValue b / 256 ^ j) := by
      funext j
      simp only [Function.comp, leValue, List.foldr_cons, pow_succ']
      rw [← Nat.div_div_eq_div_mul]
      congr 2
      omega
    rw [h0, hs, ih]

/-- A little-endian integer read is written back as the bytes it was read from. -/
theorem readLe_spec {n : ℕ} {s s' : List Byte} {x : ℕ} (h : readLe n s = some (x, s')) :
    x < 256 ^ n ∧ s = toLeBytes n (BitVec.ofNat (8 * n) x) ++ s' := by
  obtain ⟨bytes, s₁, hb, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hl := Native.readBytes_length hb
  unfold readBytes at hb
  split_ifs at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨hb, rfl⟩ := hb
  have hlt := leValue_lt bytes
  rw [hl] at hlt
  refine ⟨hlt, ?_⟩
  have hv : (BitVec.ofNat (8 * n) (leValue bytes)).toNat = leValue bytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [pow_mul]
    exact hlt
  change s = toLeBytes n (BitVec.ofNat (8 * n) (leValue bytes)) ++ s.drop n
  simp only [toLeBytes, hv]
  rw [← hl, leValue_bytes, hl, ← hb, List.take_append_drop]

/-- A little-endian integer read reads its bytes. -/
theorem consumes_readLe (n : ℕ) : Consumes (readLe n) :=
  consumes_bind (consumes_readBytes n) fun _ => consumes_pure _

/-! ## What a reader reads, its writer writes -/

/-- A `CompactSize` read is the specification's encoding of its value, at most
    `MAX_COMPACT_SIZE`. -/
theorem readCompactSize_spec {s s' : List Byte} {n : ℕ} (h : readCompactSize s = some (n, s')) :
    n ≤ MAX_COMPACT_SIZE ∧ s = Spec.compactSize (BitVec.ofNat 64 n) ++ s' := by
  obtain ⟨m, s₁, hu, h⟩ := Parser.bind_eq_some.mp h
  split at h
  · simp at h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨by omega, ?_⟩
  have hmax : m ≤ MAX_COMPACT_SIZE := by omega
  unfold MAX_COMPACT_SIZE at hmax
  obtain ⟨flag, s₂, hf, hm⟩ := Parser.bind_eq_some.mp hu
  clear hu
  obtain ⟨hflt, rfl⟩ := readLe_spec hf
  have hm64 : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  clear h hf
  split at hm
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp only [Spec.compactSize, hm64, toLeBytes, Spec.I2LEOSP]
    simp [BitVec.toNat_ofNat, show flag < 0xfd by omega]
    rw [Nat.mod_eq_of_lt (by omega)]
  split at hm
  · obtain ⟨x, s₃, hx, hk⟩ := Parser.bind_eq_some.mp hm
    obtain ⟨hxlt, rfl⟩ := readLe_spec hx
    split at hk
    · simp at hk
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Spec.compactSize, hm64]
    simp [toLeBytes, Spec.I2LEOSP, List.range_succ, BitVec.toNat_ofNat, *,
      show ¬ x < 0xfd by omega, show x ≤ 0xffff by omega,
      Nat.mod_eq_of_lt (show x < 65536 by omega)]
  split at hm
  · obtain ⟨x, s₃, hx, hk⟩ := Parser.bind_eq_some.mp hm
    obtain ⟨hxlt, rfl⟩ := readLe_spec hx
    split at hk
    · simp at hk
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Spec.compactSize, hm64]
    simp [toLeBytes, Spec.I2LEOSP, List.range_succ, BitVec.toNat_ofNat, *,
      show ¬ x < 0xfd by omega, show ¬ x ≤ 0xffff by omega, show x ≤ 0xffffffff by omega,
      Nat.mod_eq_of_lt (show x < 4294967296 by omega)]
  · obtain ⟨x, s₃, hx, hk⟩ := Parser.bind_eq_some.mp hm
    obtain ⟨hxlt, rfl⟩ := readLe_spec hx
    split at hk
    · simp at hk
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hf : flag = 255 := by omega
    subst hf
    simp only [Spec.compactSize, hm64]
    simp [toLeBytes, Spec.I2LEOSP, List.range_succ, BitVec.toNat_ofNat, *,
      show ¬ x < 0xfd by omega, show ¬ x ≤ 0xffff by omega, show ¬ x ≤ 0xffffffff by omega]

/-- `CompactSize::write` of a size at most `MAX_COMPACT_SIZE` appends its encoding. -/
theorem compactSize_write_vec (v : List Byte) {n : ℕ} (hn : n ≤ MAX_COMPACT_SIZE) :
    CompactSize.write (v : VecU8) n = .ok (v ++ Spec.compactSize (BitVec.ofNat 64 n)) := by
  simp [CompactSize.write, Nat.not_lt.mpr hn, writeUnbounded_vec]

/-- Whatever `p` reads, `write` writes back: the bytes it read, appended to any buffer. -/
def Writes {α : Type} (write : VecU8 → α → IoResult VecU8) (p : Parser α) : Prop :=
  ∀ s a s', p s = some (a, s') → ∃ w, (∀ v, write v a = .ok (v ++ w)) ∧ s = w ++ s'

/-- What `write` appends for `a`, if it appends anything. -/
def bytesOf {α : Type} (write : VecU8 → α → IoResult VecU8) (a : α) : List Byte :=
  match write [] a with
  | .ok w => w
  | .error _ => []

/-- What `write` appends to any buffer is what it appends to an empty one. -/
theorem bytesOf_eq {α : Type} {write : VecU8 → α → IoResult VecU8} {a : α} {w : List Byte}
    (h : ∀ v, write v a = .ok (v ++ w)) : bytesOf write a = w := by
  simp [bytesOf, h []]

/-- A loop of reads is written back by a fold of the writes. -/
theorem writes_readCount {α : Type} {write : VecU8 → α → IoResult VecU8} {p : Parser α}
    (hp : Writes write p) : ∀ (n : ℕ) {s s' : List Byte} {as : List α},
      readCount p n s = some (as, s') →
      (∀ v, as.foldlM write (v : VecU8) = .ok (v ++ as.flatMap (bytesOf write))) ∧
        s = as.flatMap (bytesOf write) ++ s'
  | 0, s, s', as, h => by
    change (pure [] : Parser (List α)) s = _ at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun v => by simp [pure, Except.pure], by simp⟩
  | n + 1, s, s', as, h => by
    obtain ⟨a, s₁, ha, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨as', s₂, has, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, hw, rfl⟩ := hp _ _ _ ha
    obtain ⟨hf, rfl⟩ := writes_readCount hp n has
    have hb := bytesOf_eq hw
    refine ⟨fun v => ?_, by simp [hb]⟩
    simp only [List.foldlM_cons, hw, bind, Except.bind, hf, List.flatMap_cons, hb,
      List.append_assoc]

/-- `Vector::read` is written back by `Vector::write`. -/
theorem writes_readVector {α : Type} {write : VecU8 → α → IoResult VecU8} {p : Parser α}
    (hp : Writes write p) : Writes (fun v as => Vector.write v as write) (readVector p) := by
  intro s as s' h
  obtain ⟨n, s₁, hn, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨hle, rfl⟩ := readCompactSize_spec hn
  obtain ⟨hf, rfl⟩ := writes_readCount hp n hk
  have hl := readCount_length hk
  refine ⟨Spec.compactSize (BitVec.ofNat 64 n) ++ as.flatMap (bytesOf write), fun v => ?_,
    by simp⟩
  simp only [Vector.write, hl, compactSize_write_vec v hle, bind, Except.bind, hf,
    List.append_assoc]

/-- `read_exact` into an array is written back by `write_all`. -/
theorem writes_readArr (n : ℕ) :
    Writes (fun v (a : Bytes n) => Write.writeAll v a.toList) (readArr n) := by
  intro s a s' h
  obtain ⟨b, s₁, hb, hk⟩ := Parser.bind_eq_some.mp h
  split at hk
  · simp only [pure, StateT.pure, Option.some.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨b, fun v => rfl, ?_⟩
    unfold readBytes at hb
    split_ifs at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact (List.take_append_drop n s).symm
  · simp [Native.fail] at hk

/-- A byte read is written back by `write_all`. -/
theorem writes_readByte :
    Writes (fun v (e : Byte) => Write.writeAll v [e]) (BitVec.ofNat 8 <$> readLe 1) := by
  intro s a s' h
  cases hs : readLe 1 s with
  | none => simp [Functor.map, StateT.map, hs] at h
  | some r =>
    obtain ⟨x, s₁⟩ := r
    simp only [Functor.map, StateT.map, hs, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hx, rfl⟩ := readLe_spec hs
    refine ⟨_, fun v => rfl, ?_⟩
    simp [toLeBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 256 by simpa using hx)]

/-- `Script::read` is written back by `Script::write`. -/
theorem writes_readScript : Writes (fun v (s : Transparent.Script) => s.write v) readScript := by
  intro s sc s' h
  obtain ⟨code, s₁, hc, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨w, hw, rfl⟩ := writes_readVector writes_readByte _ _ _ hc
  exact ⟨w, hw, rfl⟩

/-- `OutPoint::read` is written back by `OutPoint::write`. -/
theorem writes_readOutPoint :
    Writes (fun v (o : Transparent.OutPoint) => o.write v) readOutPoint := by
  intro s o s' h
  obtain ⟨hash, s₁, hh, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨n, s₂, hn, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨w, hw, rfl⟩ := writes_readArr 32 _ _ _ hh
  obtain rfl : hash.toList = w := by simpa [vec_write] using hw []
  obtain ⟨hlt, rfl⟩ := readLe_spec hn
  refine ⟨hash.toList ++ toLeBytes 4 (BitVec.ofNat 32 n), fun v => ?_, ?_⟩
  · simp [Transparent.OutPoint.write, vec_write, bind, Except.bind]
  · simp only [List.append_assoc]

/-- What `write` appends, for a read written back. -/
theorem writes_bytes {α : Type} {write : VecU8 → α → IoResult VecU8} {p : Parser α}
    (hp : Writes write p) {s s' : List Byte} {a : α} (h : p s = some (a, s')) :
    (∀ v, write v a = .ok (v ++ bytesOf write a)) ∧ s = bytesOf write a ++ s' := by
  obtain ⟨w, hw, rfl⟩ := hp _ _ _ h
  rw [bytesOf_eq hw]
  exact ⟨hw, rfl⟩

/-- `TxIn::read` is written back by `TxIn::write`. -/
theorem writes_readTxIn : Writes (fun v (i : Transparent.TxIn) => i.write v) readTxIn := by
  intro s i s' h
  obtain ⟨o, s₁, ho, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨sc, s₂, hs, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨n, s₃, hn, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨hwo, rfl⟩ := writes_bytes writes_readOutPoint ho
  obtain ⟨hws, rfl⟩ := writes_bytes writes_readScript hs
  obtain ⟨-, rfl⟩ := readLe_spec hn
  refine ⟨bytesOf (fun v (o : Transparent.OutPoint) => o.write v) o ++
    bytesOf (fun v (s : Transparent.Script) => s.write v) sc ++ toLeBytes 4 (BitVec.ofNat 32 n),
    fun v => ?_, by simp only [List.append_assoc]⟩
  simp only [Transparent.TxIn.write, hwo, hws, bind, Except.bind, vec_write, List.append_assoc]

/-- `TxOut::read` is written back by `TxOut::write`. -/
theorem writes_readTxOut : Writes (fun v (o : Transparent.TxOut) => o.write v) readTxOut := by
  intro s o s' h
  obtain ⟨x, s₁, hx, hk⟩ := Parser.bind_eq_some.mp h
  dsimp only at hk
  split at hk
  · simp at hk
  obtain ⟨sc, s₂, hs, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨hws, rfl⟩ := writes_bytes writes_readScript hs
  obtain ⟨-, rfl⟩ := readLe_spec hx
  refine ⟨toLeBytes 8 (BitVec.ofNat 64 x) ++
    bytesOf (fun v (s : Transparent.Script) => s.write v) sc, fun v => ?_,
    by simp only [List.append_assoc]⟩
  simp only [Transparent.TxOut.write, hws, bind, Except.bind, vec_write, List.append_assoc]

/-- `read_transparent` is written back by `write_transparent`. -/
theorem readTransparent_writes {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {ob : Option Transparent.Bundle} (h : readTransparent ctx s = some (ob, s')) :
    ∃ w, (∀ tx : TransactionData, tx.transparentBundle = ob →
      ∀ v, tx.writeTransparent (v : VecU8) = .ok (v ++ w)) ∧ s = w ++ s' := by
  obtain ⟨vin, s₁, hi, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨vout, s₂, ho, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨hwi, rfl⟩ := writes_bytes (writes_readVector writes_readTxIn) hi
  obtain ⟨hwo, rfl⟩ := writes_bytes (writes_readVector writes_readTxOut) ho
  refine ⟨_, fun tx htx v => ?_, (List.append_assoc _ _ _).symm⟩
  by_cases he : vin.isEmpty && vout.isEmpty
  · simp only [he, ite_true] at htx
    simp only [Bool.and_eq_true, List.isEmpty_iff] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [TransactionData.writeTransparent, htx, compactSize_write_vec _ (Nat.zero_le _),
      bind, Except.bind, List.append_assoc]
    rfl
  · simp only [he, Bool.false_eq_true, ite_false] at htx
    simp only [TransactionData.writeTransparent, htx]
    simp only [hwi v, bind, Except.bind, hwo, List.append_assoc]

/-! ## Sapling -/

/-- A reader whose reads are their encodings `e`. -/
theorem writes_enc {α : Type} {p : Parser α} (e : α → List Byte)
    (h : ∀ s a s', p s = some (a, s') → s = e a ++ s') :
    Writes (fun v a => Write.writeAll (v : VecU8) (e a)) p :=
  fun s a s' hs => ⟨e a, fun _ => rfl, h s a s' hs⟩

/-- An array read is its bytes. -/
theorem readArr_enc {n : ℕ} {s s' : List Byte} {a : Bytes n} (h : readArr n s = some (a, s')) :
    s = a.toList ++ s' := by
  obtain ⟨w, hw, rfl⟩ := writes_readArr n _ _ _ h
  obtain rfl : a.toList = w := by simpa [vec_write] using hw []
  rfl

/-- A loop of array reads is their bytes. -/
theorem readCount_arr {n : ℕ} (k : ℕ) {s s' : List Byte} {as : List (Bytes n)}
    (h : readCount (readArr n) k s = some (as, s')) : s = as.flatMap (·.toList) ++ s' :=
  (writes_readCount (writes_enc (fun a : Bytes n => a.toList) fun _ _ _ h => readArr_enc h) k
    h).2

/-- The fields of a Spend, as `read_spend_v5` reads them. -/
def spendV5Bytes (t : Bytes 32 × Bytes 32 × Bytes 32) : List Byte :=
  t.1.toList ++ t.2.1.toList ++ t.2.2.toList

/-- `read_spend_v5` reads the fields it returns. -/
theorem readSpendV5_enc {s s' : List Byte} {t : Bytes 32 × Bytes 32 × Bytes 32}
    (h : readSpendV5 s = some (t, s')) : s = spendV5Bytes t ++ s' := by
  obtain ⟨cv, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨nf, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨rk, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  rw [readArr_enc h₁, readArr_enc h₂, readArr_enc h₃]
  simp [spendV5Bytes]

/-- The fields of an Output, as `read_output_v5` reads them. -/
def outputV5Bytes (t : Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80) : List Byte :=
  t.1.toList ++ t.2.1.toList ++ t.2.2.1.toList ++ t.2.2.2.1.toList ++ t.2.2.2.2.toList

/-- `read_output_v5` reads the fields it returns. -/
theorem readOutputV5_enc {s s' : List Byte}
    {t : Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80}
    (h : readOutputV5 s = some (t, s')) : s = outputV5Bytes t ++ s' := by
  obtain ⟨cv, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨cmu, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨epk, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨enc, s₄, h₄, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨out, s₅, h₅, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  rw [readArr_enc h₁, readArr_enc h₂, readArr_enc h₃, readArr_enc h₄, readArr_enc h₅]
  simp [outputV5Bytes]

/-- A `Vector::read` of encodings is their count, then their encodings. -/
theorem readVector_enc {α : Type} {p : Parser α} (e : α → List Byte)
    (he : ∀ s a s', p s = some (a, s') → s = e a ++ s') {s s' : List Byte} {as : List α}
    (h : readVector p s = some (as, s')) :
    as.length ≤ MAX_COMPACT_SIZE ∧
      s = Spec.compactSize (BitVec.ofNat 64 as.length) ++ as.flatMap e ++ s' := by
  obtain ⟨n, s₁, hn, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨hle, rfl⟩ := readCompactSize_spec hn
  have hl := readCount_length hk
  obtain ⟨-, rfl⟩ := writes_readCount (writes_enc e he) n hk
  subst hl
  exact ⟨hle, by simp only [List.append_assoc]; rfl⟩

/-- `Vector::write` of a list each of whose elements `func` writes as `e`. -/
theorem vector_write_vec {α : Type} (v : List Byte) (l : List α) (e : α → List Byte)
    (func : VecU8 → α → IoResult VecU8) (hf : ∀ a ∈ l, ∀ y, func y a = .ok (y ++ e a))
    (hl : l.length ≤ MAX_COMPACT_SIZE) :
    Vector.write (v : VecU8) l func =
      .ok (v ++ Spec.compactSize (BitVec.ofNat 64 l.length) ++ l.flatMap e) := by
  simp only [Vector.write, compactSize_write_vec v hl, bind, Except.bind]
  exact foldlM_vec l _ e func hf

/-- Mapping a zip onto its first component's function. -/
theorem flatMap_map_zip {α β γ : Type} (l : List α) (m : List β) (g : α × β → γ)
    (f : γ → List Byte) (f' : α → List Byte) (hg : ∀ a b, f (g (a, b)) = f' a)
    (hl : l.length ≤ m.length) : ((l.zip m).map g).flatMap f = l.flatMap f' := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | nil => simp at hl
    | cons b m =>
      simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons, hg]
      rw [ih m (by simpa using hl)]

/-- Mapping a zip onto its second component's function. -/
theorem flatMap_map_zip_right {α β γ : Type} (l : List α) (m : List β) (g : α × β → γ)
    (f : γ → List Byte) (f' : β → List Byte) (hg : ∀ a b, f (g (a, b)) = f' b)
    (hl : m.length ≤ l.length) : ((l.zip m).map g).flatMap f = m.flatMap f' := by
  induction m generalizing l with
  | nil => simp
  | cons b m ih =>
    cases l with
    | nil => simp at hl
    | cons a l =>
      simp only [List.zip_cons_cons, List.map_cons, List.flatMap_cons, hg]
      rw [ih l (by simpa using hl)]

/-- A zip's first components. -/
theorem flatMap_zip_left {α β : Type} (l : List α) (m : List β) (f : α → List Byte)
    (hl : l.length ≤ m.length) : (l.zip m).flatMap (fun x => f x.1) = l.flatMap f := by
  simpa using flatMap_map_zip l m id (fun x => f x.1) f (fun _ _ => rfl) hl

/-- A zip's second components. -/
theorem flatMap_zip_right {α β : Type} (l : List α) (m : List β) (f : β → List Byte)
    (hl : m.length ≤ l.length) : (l.zip m).flatMap (fun x => f x.2) = m.flatMap f := by
  simpa using flatMap_map_zip_right l m id (fun x => f x.2) f (fun _ _ => rfl) hl

/-- `read_amount` reads the little-endian bytes of the value balance it returns. -/
theorem readAmount_enc {s s' : List Byte} {v : BitVec 64} (h : readAmount s = some (v, s')) :
    s = toLeBytes 8 v ++ s' := by
  obtain ⟨x, s₁, hx, hk⟩ := Parser.bind_eq_some.mp h
  split at hk
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact (readLe_spec hx).2
  · simp at hk

/-- A value read only under a condition: read, or the default, reading nothing. -/
theorem readIf_spec {α : Type} {c : Bool} {p : Parser α} {d : α} {s s' : List Byte} {a : α}
    (h : readIf c p d s = some (a, s')) : (c = true ∧ p s = some (a, s')) ∨
      (c = false ∧ a = d ∧ s' = s) := by
  unfold readIf at h
  cases c
  · simp only [Bool.false_eq_true, ite_false, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    exact .inr ⟨rfl, h.1.symm, h.2.symm⟩
  · exact .inl ⟨rfl, h⟩

/-- An optional array read. -/
theorem someArr_enc {n : ℕ} {s s' : List Byte} {a : Option (Bytes n)}
    (h : (some <$> readArr n) s = some (a, s')) : ∃ b, a = some b ∧ s = b.toList ++ s' := by
  cases hs : readArr n s with
  | none => simp [Functor.map, StateT.map, hs] at h
  | some r =>
    obtain ⟨b, s₁⟩ := r
    simp only [Functor.map, StateT.map, hs, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, rfl, readArr_enc hs⟩

/-- The fields `write_spend_v5_without_witness_data` writes. -/
def spendDescBytes (s : Sapling.SpendDescription) : List Byte :=
  s.cv.toList ++ s.nullifier.toList ++ s.rk.toList

/-- The fields `write_output_v5_without_proof` writes. -/
def outputDescBytes (o : Sapling.OutputDescription) : List Byte :=
  o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList ++
    o.outCiphertext.toList

/-- `write_v5_bundle` of a bundle with a Spend or an Output: its counts and descriptions, its
    value balance, its first Spend's anchor if it has one, its proofs and signatures, and its
    binding signature. -/
theorem writeSaplingV5_some (v : List Byte) (b : Sapling.Bundle)
    (hs : b.shieldedSpends.length ≤ MAX_COMPACT_SIZE)
    (ho : b.shieldedOutputs.length ≤ MAX_COMPACT_SIZE)
    (hne : b.shieldedSpends ≠ [] ∨ b.shieldedOutputs ≠ []) :
    writeSaplingV5 (v : VecU8) (some b) = .ok (v ++
      Spec.compactSize (BitVec.ofNat 64 b.shieldedSpends.length) ++
      b.shieldedSpends.flatMap spendDescBytes ++
      Spec.compactSize (BitVec.ofNat 64 b.shieldedOutputs.length) ++
      b.shieldedOutputs.flatMap outputDescBytes ++ toLeBytes 8 b.valueBalance ++
      (b.shieldedSpends.head?.map (·.anchor.toList)).getD [] ++
      b.shieldedSpends.flatMap (·.zkproof.toList) ++
      b.shieldedSpends.flatMap (·.spendAuthSig.toList) ++
      b.shieldedOutputs.flatMap (·.zkproof.toList) ++ b.bindingSig.toList) := by
  rcases b with ⟨sp, op, vb, sig⟩
  have warr {n : ℕ} (l : List (Bytes n)) (v : List Byte) :
      Array.write (v : VecU8) l (fun w e => .ok (w ++ e.toList)) =
        .ok (v ++ l.flatMap (·.toList)) :=
    foldlM_vec l v (·.toList) _ fun _ _ y => rfl
  have wsp : ∀ v, Vector.write (v : VecU8) sp writeSpendV5WithoutWitnessData =
      .ok (v ++ Spec.compactSize (BitVec.ofNat 64 sp.length) ++ sp.flatMap spendDescBytes) :=
    fun v => vector_write_vec v sp spendDescBytes _
      (fun s _ y => by simp [writeSpendV5WithoutWitnessData, spendDescBytes, vec_write, bind,
        Except.bind]) hs
  have wop : ∀ v, Vector.write (v : VecU8) op writeOutputV5WithoutProof =
      .ok (v ++ Spec.compactSize (BitVec.ofNat 64 op.length) ++ op.flatMap outputDescBytes) :=
    fun v => vector_write_vec v op outputDescBytes _
      (fun o _ y => by simp [writeOutputV5WithoutProof, outputDescBytes, vec_write, bind,
        Except.bind]) ho
  cases sp with
  | nil =>
    have hop : op ≠ [] := by simpa using hne
    simp [writeSaplingV5, wsp, wop, hop, bind, Except.bind, vec_write, warr, List.flatMap_map,
      pure, Except.pure]
  | cons s sp =>
    simp [writeSaplingV5, wsp, wop, bind, Except.bind, vec_write, warr, List.flatMap_map]

/-- `read_v5_bundle` is written back by `write_v5_bundle`. -/
theorem readSaplingV5_writes {s s' : List Byte} {ob : Option Sapling.Bundle}
    (h : readSaplingV5 s = some (ob, s')) :
    ∃ w, (∀ v, writeSaplingV5 (v : VecU8) ob = .ok (v ++ w)) ∧ s = w ++ s' := by
  obtain ⟨sds, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨ods, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨vb, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨anchor, s₄, h₄, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨sps, s₅, h₅, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨sss, s₆, h₆, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨ops, s₇, h₇, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨bsig, s₈, h₈, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨hls, rfl⟩ := readVector_enc spendV5Bytes (fun _ _ _ h => readSpendV5_enc h) h₁
  obtain ⟨hlo, rfl⟩ := readVector_enc outputV5Bytes (fun _ _ _ h => readOutputV5_enc h) h₂
  have hl₅ := readCount_length h₅
  have hl₆ := readCount_length h₆
  have hl₇ := readCount_length h₇
  have e₅ := readCount_arr _ h₅
  have e₆ := readCount_arr _ h₆
  have e₇ := readCount_arr _ h₇
  subst e₇ e₆ e₅
  clear h₅ h₆ h₇
  -- The Spends and Outputs the reader builds, and what writing them writes.
  set spends := (sds.zip (sps.zip sss)).map fun ((cv, nullifier, rk), (zkproof, spendAuthSig)) =>
    (⟨cv, anchor.getD (List.Vector.replicate 32 0), nullifier, rk, zkproof, spendAuthSig⟩ :
      Sapling.SpendDescription) with hspends
  set outputs := (ods.zip ops).map
    fun ((cv, cmu, ephemeralKey, encCiphertext, outCiphertext), zkproof) =>
      (⟨cv, cmu, ephemeralKey, encCiphertext, outCiphertext, zkproof⟩ :
        Sapling.OutputDescription) with houtputs
  have hlsp : spends.length = sds.length := by simp [hspends, hl₅, hl₆]
  have hlop : outputs.length = ods.length := by simp [houtputs, hl₇]
  have hspd : spends.flatMap spendDescBytes = sds.flatMap spendV5Bytes := by
    rw [hspends]
    exact flatMap_map_zip _ _ _ _ spendV5Bytes (fun _ _ => rfl) (by simp [hl₅, hl₆])
  have hopd : outputs.flatMap outputDescBytes = ods.flatMap outputV5Bytes := by
    rw [houtputs]
    exact flatMap_map_zip _ _ _ _ outputV5Bytes (fun _ _ => by simp [outputDescBytes,
      outputV5Bytes]) (by simp [hl₇])
  have hsps : spends.flatMap (·.zkproof.toList) = sps.flatMap (·.toList) := by
    rw [hspends, flatMap_map_zip_right _ _ _ _ (fun x => x.1.toList)
      (fun _ _ => rfl) (by simp [hl₅, hl₆])]
    exact flatMap_zip_left _ _ (fun x : Bytes 192 => x.toList) (by omega)
  have hsss : spends.flatMap (·.spendAuthSig.toList) = sss.flatMap (·.toList) := by
    rw [hspends, flatMap_map_zip_right _ _ _ _ (fun x => x.2.toList)
      (fun _ _ => rfl) (by simp [hl₅, hl₆])]
    exact flatMap_zip_right _ _ (fun x : Bytes 64 => x.toList) (by omega)
  have hops : outputs.flatMap (·.zkproof.toList) = ops.flatMap (·.toList) := by
    rw [houtputs]
    exact flatMap_map_zip_right _ _ _ _ (fun x : Bytes 192 => x.toList) (fun _ _ => rfl)
      (by omega)
  rcases readIf_spec h₃ with ⟨hc, h₃⟩ | ⟨hc, rfl, rfl⟩
  · -- A Spend or an Output: the value balance, the binding signature and the bundle.
    have e₃ := readAmount_enc h₃
    subst e₃
    rcases readIf_spec h₈ with ⟨-, h₈⟩ | ⟨hc', -⟩
    swap
    · rw [hc] at hc'; cases hc'
    obtain ⟨sig, rfl, rfl⟩ := someArr_enc h₈
    have hne : ¬(spends.isEmpty && outputs.isEmpty) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      simp only [Bool.and_eq_true, List.isEmpty_iff, not_and, ← List.length_eq_zero_iff, hlsp,
        hlop]
      omega
    have hb : (some sig).bind (saplingFromParts spends outputs vb) =
        some ⟨spends, outputs, vb, sig⟩ := by
      simp [saplingFromParts, hne]
    rw [hb]
    -- The anchor: read, and written from the first Spend, exactly when there is a Spend.
    have hanchor : (spends.head?.map (·.anchor.toList)).getD [] =
        (anchor.map (·.toList)).getD [] := by
      rcases readIf_spec h₄ with ⟨hc₄, h₄'⟩ | ⟨hc₄, rfl, -⟩
      · obtain ⟨a, rfl, -⟩ := someArr_enc h₄'
        obtain ⟨d, ds, rfl⟩ : ∃ d ds, sds = d :: ds :=
          List.exists_cons_of_ne_nil (by simp at hc₄; exact List.ne_nil_of_length_pos hc₄)
        obtain ⟨p, ps, rfl⟩ : ∃ p ps, sps = p :: ps :=
          List.exists_cons_of_ne_nil (by rintro rfl; simp at hl₅)
        obtain ⟨g, gs, rfl⟩ : ∃ g gs, sss = g :: gs :=
          List.exists_cons_of_ne_nil (by rintro rfl; simp at hl₆)
        simp [hspends]
      · have : sds = [] := by simpa using hc₄
        subst this
        simp [hspends]
    have e₄ : s₃ = (anchor.map (·.toList)).getD [] ++ (sps.flatMap (·.toList) ++
        (sss.flatMap (·.toList) ++ (ops.flatMap (·.toList) ++ (sig.toList ++ s₈)))) := by
      rcases readIf_spec h₄ with ⟨-, h₄'⟩ | ⟨-, rfl, h₄'⟩
      · obtain ⟨a, rfl, ha⟩ := someArr_enc h₄'
        simpa using ha
      · simpa using h₄'.symm
    subst e₄
    refine ⟨Spec.compactSize (BitVec.ofNat 64 sds.length) ++ sds.flatMap spendV5Bytes ++
      Spec.compactSize (BitVec.ofNat 64 ods.length) ++ ods.flatMap outputV5Bytes ++
      toLeBytes 8 vb ++ (anchor.map (·.toList)).getD [] ++ sps.flatMap (·.toList) ++
      sss.flatMap (·.toList) ++ ops.flatMap (·.toList) ++ sig.toList, fun v => ?_,
      by simp only [List.append_assoc]⟩
    rw [writeSaplingV5_some v _ (by simpa [hlsp] using hls) (by simpa [hlop] using hlo)
      (by simpa [List.isEmpty_iff, or_iff_not_imp_left] using hne)]
    simp only [hlsp, hlop, hanchor, hspd, hopd, hsps, hsss, hops, List.append_assoc]
  · -- No Spend or Output: no value balance, anchor, proofs, signatures or bundle.
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt, Nat.le_zero,
      List.length_eq_zero_iff] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : sps = [] := List.length_eq_zero_iff.mp (by simpa using hl₅)
    obtain rfl : sss = [] := List.length_eq_zero_iff.mp (by simpa using hl₆)
    obtain rfl : ops = [] := List.length_eq_zero_iff.mp (by simpa using hl₇)
    rcases readIf_spec h₄ with ⟨hc₄, -⟩ | ⟨-, rfl, he₄⟩
    · simp at hc₄
    rcases readIf_spec h₈ with ⟨hc₈, -⟩ | ⟨-, rfl, rfl⟩
    · simp at hc₈
    simp only [List.flatMap_nil, List.nil_append] at he₄
    subst he₄
    refine ⟨Spec.compactSize 0 ++ Spec.compactSize 0, fun v => ?_, by simp⟩
    simp [writeSaplingV5, compactSize_write_vec _ (Nat.zero_le _), bind, Except.bind]

/-! ## Orchard -/

/-- The fields of an Action, as `read_action_without_auth` reads them. -/
def actionBytes (t : Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80) :
    List Byte :=
  t.1.toList ++ t.2.1.toList ++ t.2.2.1.toList ++ t.2.2.2.1.toList ++ t.2.2.2.2.1.toList ++
    t.2.2.2.2.2.1.toList ++ t.2.2.2.2.2.2.toList

/-- The fields `write_action_without_auth` writes. -/
def actionDescBytes (a : Orchard.Action) : List Byte :=
  a.cvNet.toList ++ a.nf.toList ++ a.rk.toList ++ a.cmx.toList ++ a.epkBytes.toList ++
    a.encCiphertext.toList ++ a.outCiphertext.toList

/-- `read_action_without_auth` reads the fields it returns. -/
theorem readActionWithoutAuth_enc {s s' : List Byte}
    {t : Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80}
    (h : readActionWithoutAuth s = some (t, s')) : s = actionBytes t ++ s' := by
  obtain ⟨a₁, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨a₂, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨a₃, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨a₄, s₄, h₄, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨a₅, s₅, h₅, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨a₆, s₆, h₆, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨a₇, s₇, h₇, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  rw [readArr_enc h₁, readArr_enc h₂, readArr_enc h₃, readArr_enc h₄, readArr_enc h₅,
    readArr_enc h₆, readArr_enc h₇]
  simp [actionBytes]

/-- A byte vector read is its length, then its bytes. -/
theorem readByteVector_enc {s s' : List Byte} {b : List Byte}
    (h : readVector (BitVec.ofNat 8 <$> readLe 1) s = some (b, s')) :
    b.length ≤ MAX_COMPACT_SIZE ∧ s = Spec.compactSize (BitVec.ofNat 64 b.length) ++ b ++ s' := by
  have := readVector_enc (fun e => [e]) (fun s a s' h => by
    obtain ⟨w, hw, rfl⟩ := writes_readByte s a s' h
    obtain rfl : [a] = w := by simpa [vec_write] using hw []
    rfl) h
  simpa using this

/-- `write_bundle` of an Orchard-shaped bundle. -/
theorem writeOrchardBundle_some (v : List Byte) (b : Orchard.Bundle)
    (hl : b.actions.toList.length ≤ MAX_COMPACT_SIZE) (hp : b.proof.length ≤ MAX_COMPACT_SIZE) :
    writeOrchardBundle (some b) (v : VecU8) = .ok (v ++
      Spec.compactSize (BitVec.ofNat 64 b.actions.toList.length) ++
      b.actions.toList.flatMap actionDescBytes ++ [b.flagByte] ++ toLeBytes 8 b.valueBalance ++
      b.anchor.toList ++ Spec.compactSize (BitVec.ofNat 64 b.proof.length) ++ b.proof ++
      b.actions.toList.flatMap (·.authorization.toList) ++ b.bindingSignature.toList) := by
  have hacts : ∀ y, b.actions.toList.foldlM writeActionWithoutAuth (y : VecU8) =
      .ok (y ++ b.actions.toList.flatMap actionDescBytes) :=
    fun y => foldlM_vec _ y actionDescBytes _ fun a _ z => by
      simp [writeActionWithoutAuth, actionDescBytes, vec_write, bind, Except.bind]
  have hproof : ∀ y, Vector.write (y : VecU8) b.proof (fun w e => .ok (w ++ [e])) =
      .ok (y ++ Spec.compactSize (BitVec.ofNat 64 b.proof.length) ++ b.proof) := by
    intro y
    rw [vector_write_vec y b.proof (fun e => [e]) _ (fun _ _ z => rfl) hp]
    simp
  have hauth : ∀ y, Array.write (y : VecU8) (b.actions.toList.map (·.authorization))
      (fun w auth => .ok (w ++ auth.toList)) =
      .ok (y ++ b.actions.toList.flatMap (·.authorization.toList)) := by
    intro y
    unfold Array.write
    rw [foldlM_vec _ y (fun x : Bytes 64 => x.toList) _ (fun _ _ z => rfl), List.flatMap_map]
  simp [writeOrchardBundle, compactSize_write_vec _ hl, bind, Except.bind, hacts, vec_write,
    hproof, hauth]

/-- `read_bundle` is written back by `write_bundle`. -/
theorem readOrchardBundle_writes {pool : Orchard.ValuePool} {s s' : List Byte}
    {ob : Option Orchard.Bundle} (h : readOrchardBundle pool s = some (ob, s')) :
    ∃ w, (∀ v, writeOrchardBundle ob (v : VecU8) = .ok (v ++ w)) ∧ s = w ++ s' := by
  obtain ⟨awa, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨hla, rfl⟩ := readVector_enc actionBytes (fun _ _ _ h => readActionWithoutAuth_enc h) h₁
  split at hk
  · rename_i he
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain rfl : awa = [] := List.isEmpty_iff.mp he
    exact ⟨Spec.compactSize 0, fun v => by simp [writeOrchardBundle, compactSize_write_vec],
      by simp⟩
  · obtain ⟨flags, s₂, h₂, k₂⟩ := Parser.bind_eq_some.mp hk
    obtain ⟨vb, s₃, h₃, k₃⟩ := Parser.bind_eq_some.mp k₂
    obtain ⟨anchor, s₄, h₄, k₄⟩ := Parser.bind_eq_some.mp k₃
    obtain ⟨proof, s₅, h₅, k₅⟩ := Parser.bind_eq_some.mp k₄
    obtain ⟨sigs, s₆, h₆, k₆⟩ := Parser.bind_eq_some.mp k₅
    obtain ⟨bsig, s₇, h₇, k₇⟩ := Parser.bind_eq_some.mp k₆
    clear hk k₂ k₃ k₄ k₅ k₆
    have hl₆ := readCount_length h₆
    have hpl := (readByteVector_enc h₅).1
    have hfl := (readLe_spec h₂).1
    rw [(readLe_spec h₂).2, readAmount_enc h₃, readArr_enc h₄, (readByteVector_enc h₅).2,
      readCount_arr _ h₆, readArr_enc h₇]
    dsimp only at k₇
    generalize hacts : (awa.zip sigs).map _ = acts at k₇
    cases hn : nonEmptyFromVec acts with
    | none => rw [hn] at k₇; simp [Native.fail] at k₇
    | some ne =>
      rw [hn] at k₇
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at k₇
      obtain ⟨rfl, rfl⟩ := k₇
      have hne' : ne.toList = acts := by
        cases acts with
        | nil => simp [nonEmptyFromVec] at hn
        | cons a as =>
          simp only [nonEmptyFromVec, Option.some.injEq] at hn
          subst hn; rfl
      have hlen : ne.toList.length = awa.length := by
        rw [hne', ← hacts]; simp [hl₆]
      have hd : ne.toList.flatMap actionDescBytes = awa.flatMap actionBytes := by
        rw [hne', ← hacts]
        exact flatMap_map_zip _ _ _ _ actionBytes (fun _ _ => by simp [actionDescBytes,
          actionBytes]) (by omega)
      have hs : ne.toList.flatMap (·.authorization.toList) = sigs.flatMap (·.toList) := by
        rw [hne', ← hacts]
        exact flatMap_map_zip_right _ _ _ _ (fun x : Bytes 64 => x.toList) (fun _ _ => rfl)
          (by omega)
      refine ⟨Spec.compactSize (BitVec.ofNat 64 ne.toList.length) ++
        ne.toList.flatMap actionDescBytes ++ [BitVec.ofNat 8 flags] ++ toLeBytes 8 vb ++
        anchor.toList ++ Spec.compactSize (BitVec.ofNat 64 proof.length) ++ proof ++
        ne.toList.flatMap (·.authorization.toList) ++ bsig.toList, fun v => ?_, ?_⟩
      · rw [writeOrchardBundle_some v ⟨ne, BitVec.ofNat 8 flags, vb, anchor, proof, bsig, pool⟩
          (by simpa [hlen] using hla) hpl]
        simp only [List.append_assoc]
      simp only [hlen, hd, hs, List.append_assoc]
      simp [toLeBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show flags < 256 by simpa using hfl)]

/-! ## The readers consume what they read -/

/-- Applies the consumption lemmas through a reader's definition. -/
macro "consumes_tac" : tactic => `(tactic| (
  repeat' (first
    | assumption
    | exact consumes_pure _
    | exact consumes_fail
    | exact consumes_readBytes _
    | exact consumes_readLe _
    | refine consumes_bind ?_ fun _ => ?_
    | refine consumes_map _ ?_
    | dsimp only
    | split)))

/-- `CompactSize::read` consumes its input. -/
theorem consumes_readCompactSize : Consumes readCompactSize := by
  unfold readCompactSize readCompactSizeUnbounded
  consumes_tac

/-- An array read consumes its input. -/
theorem consumes_readArr (n : ℕ) : Consumes (readArr n) := by
  unfold readArr
  consumes_tac

/-- `Vector::read` of reads that consume their input consumes its input. -/
theorem consumes_readVector {α : Type} {p : Parser α} (hp : Consumes p) :
    Consumes (readVector p) :=
  consumes_bind consumes_readCompactSize fun n => consumes_readCount hp n

/-- A value read under a condition consumes its input. -/
theorem consumes_readIf {α : Type} (c : Bool) {p : Parser α} (d : α) (hp : Consumes p) :
    Consumes (readIf c p d) := by
  unfold readIf
  split
  · exact hp
  · exact consumes_pure d

/-- `read_transparent` consumes its input. -/
theorem consumes_readTransparent (ctx : Transparent.AuthorizingContext) :
    Consumes (readTransparent ctx) := by
  have hb := consumes_map (BitVec.ofNat 8) (consumes_readLe 1)
  have hv := consumes_readVector hb
  have hs : Consumes readScript := by unfold readScript; consumes_tac
  have ha := consumes_readArr 32
  have hi : Consumes readTxIn := by unfold readTxIn readOutPoint; consumes_tac
  have ho : Consumes readTxOut := by unfold readTxOut; consumes_tac
  have hvi := consumes_readVector hi
  have hvo := consumes_readVector ho
  unfold readTransparent
  consumes_tac

/-- `read_amount` consumes its input. -/
theorem consumes_readAmount : Consumes readAmount := by
  unfold readAmount
  consumes_tac

/-- `read_v5_bundle` consumes its input. -/
theorem consumes_readSaplingV5 : Consumes readSaplingV5 := by
  have hs : Consumes readSpendV5 := by
    have := consumes_readArr 32
    unfold readSpendV5; consumes_tac
  have ho : Consumes readOutputV5 := by
    have := consumes_readArr 32
    have := consumes_readArr 580
    have := consumes_readArr 80
    unfold readOutputV5; consumes_tac
  have := consumes_readVector hs
  have := consumes_readVector ho
  unfold readSaplingV5
  refine consumes_bind (by assumption) fun _ => consumes_bind (by assumption) fun _ =>
    consumes_bind (consumes_readIf _ _ consumes_readAmount) fun _ => consumes_bind
      (consumes_readIf _ _ (consumes_map _ (consumes_readArr 32))) fun _ => consumes_bind
      (consumes_readCount (consumes_readArr 192) _) fun _ => consumes_bind
      (consumes_readCount (consumes_readArr 64) _) fun _ => consumes_bind
      (consumes_readCount (consumes_readArr 192) _) fun _ => consumes_bind
      (consumes_readIf _ _ (consumes_map _ (consumes_readArr 64))) fun _ => consumes_pure _

/-- `read_bundle` consumes its input. -/
theorem consumes_readOrchardBundle (pool : Orchard.ValuePool) :
    Consumes (readOrchardBundle pool) := by
  have hact : Consumes readActionWithoutAuth := by
    have := consumes_readArr 32
    have := consumes_readArr 580
    have := consumes_readArr 80
    unfold readActionWithoutAuth; consumes_tac
  have := consumes_readVector hact
  have := consumes_readAmount
  have := consumes_readArr 32
  have := consumes_readArr 64
  have := consumes_readVector (consumes_map (BitVec.ofNat 8) (consumes_readLe 1))
  have hc : ∀ n, Consumes (readCount (readArr 64) n) := consumes_readCount (consumes_readArr 64)
  unfold readOrchardBundle
  refine consumes_bind (by assumption) fun _ => ?_
  split
  · exact consumes_pure _
  · refine consumes_bind (consumes_readLe 1) fun _ => consumes_bind consumes_readAmount fun _ =>
      consumes_bind (consumes_readArr 32) fun _ => consumes_bind (by assumption) fun _ =>
      consumes_bind (hc _) fun _ => consumes_bind (consumes_readArr 64) fun _ => ?_
    consumes_tac

/-- `read_header_fragment` consumes its input. -/
theorem consumes_readHeaderFragment : Consumes readHeaderFragment := by
  unfold readHeaderFragment
  consumes_tac

/-- `read_v5` consumes its input. -/
theorem consumes_readV5 (ctx : Transparent.AuthorizingContext) (v : TxVersion) :
    Consumes (readV5 ctx v) :=
  consumes_bind consumes_readHeaderFragment fun _ => consumes_bind
    (consumes_readTransparent ctx) fun _ => consumes_bind consumes_readSaplingV5 fun _ =>
    consumes_bind (consumes_readOrchardBundle .orchard) fun _ => consumes_pure _

/-- `read_v6` consumes its input. -/
theorem consumes_readV6 (ctx : Transparent.AuthorizingContext) (v : TxVersion) :
    Consumes (readV6 ctx v) :=
  consumes_bind consumes_readHeaderFragment fun _ => consumes_bind
    (consumes_readTransparent ctx) fun _ => consumes_bind consumes_readSaplingV5 fun _ =>
    consumes_bind (consumes_readOrchardBundle .orchard) fun _ =>
    consumes_bind (consumes_readOrchardBundle .ironwood) fun _ => consumes_pure _

/-- `Transaction::read` consumes its input. -/
theorem consumes_read (ctx : Transparent.AuthorizingContext) : Consumes (read ctx) := by
  have hv : Consumes readTxVersion := by unfold readTxVersion; consumes_tac
  have := consumes_readV5 ctx .v5
  have := consumes_readV6 ctx .v6
  unfold read
  refine consumes_bind hv fun v => ?_
  cases v <;> consumes_tac

/-! ## Transactions -/

/-- `read_header_fragment` reads the bytes `write_v5_header` writes after the version. -/
theorem readHeaderFragment_enc {s s' : List Byte} {r : BitVec 32 × BitVec 32 × BitVec 32}
    (h : readHeaderFragment s = some (r, s')) :
    s = toLeBytes 4 r.1 ++ toLeBytes 4 r.2.1 ++ toLeBytes 4 r.2.2 ++ s' := by
  obtain ⟨b, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨l, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨e, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  rw [(readLe_spec h₁).2, (readLe_spec h₂).2, (readLe_spec h₃).2]
  simp only [List.append_assoc]

/-- A version 5 transaction's header and bundles, as `read_v5` reads them and `write_v5` writes
    them after the version. -/
theorem readV5_writes {ctx : Transparent.AuthorizingContext} {v : TxVersion} {s s' : List Byte}
    {tx : TransactionData} (h : readV5 ctx v s = some (tx, s')) :
    ∃ w, (∀ buf, tx.writeV5 (buf : VecU8) = .ok (buf ++ tx.version.write ++ w)) ∧
      s = w ++ s' := by
  obtain ⟨r, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨t, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨sap, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨orc, s₄, h₄, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨b, c, d⟩ := r
  obtain ⟨wt, hwt, rfl⟩ := readTransparent_writes h₂
  obtain ⟨ws, hws, rfl⟩ := readSaplingV5_writes h₃
  obtain ⟨wo, hwo, rfl⟩ := readOrchardBundle_writes h₄
  rw [readHeaderFragment_enc h₁]
  refine ⟨toLeBytes 4 b ++ toLeBytes 4 c ++ toLeBytes 4 d ++ wt ++ ws ++ wo, fun buf => ?_,
    by simp only [List.append_assoc]⟩
  have hwt' := hwt ⟨v, b, c, d, t, none, sap, orc, none⟩ rfl
  simp only [TransactionData.writeV5, TransactionData.writeV5Header, Option.isSome_none,
    Bool.false_eq_true, ite_false, bind, Except.bind, vec_write, hwt', hws, hwo,
    List.append_assoc]

/-- Under a branch of the third Orchard protocol revision (NU6.3 and NU7), `write_v6_bundle`
    accepts a bundle of either pool, and writes it as `write_bundle` does. -/
theorem writeV6OrchardBundle_eq {branchId : BitVec 32} {ob : Option Orchard.Bundle}
    (hrev : ob.isSome → orchardProtocolRevision branchId = some .v3) (buf : VecU8) :
    writeV6OrchardBundle branchId ob buf = writeOrchardBundle ob buf := by
  cases ob with
  | none => rfl
  | some b =>
    have hrev := hrev rfl
    cases hp : b.valuePool <;>
      simp [writeV6OrchardBundle, bundleVersionForBranch, hrev, hp, checkV6BundleVersion, bind,
        Except.bind]

/-- A version 6 transaction's header and bundles, as `read_v6` reads them and `write_v6` writes
    them after the version, if it has an Orchard or Ironwood bundle under a branch of the third
    Orchard protocol revision. -/
theorem readV6_writes {ctx : Transparent.AuthorizingContext} {v : TxVersion} {s s' : List Byte}
    {tx : TransactionData} (h : readV6 ctx v s = some (tx, s'))
    (hrev : tx.orchardBundle.isSome ∨ tx.ironwoodBundle.isSome →
      orchardProtocolRevision tx.consensusBranchId = some .v3) :
    ∃ w, (∀ buf, tx.writeV6 (buf : VecU8) = .ok (buf ++ tx.version.write ++ w)) ∧
      s = w ++ s' := by
  obtain ⟨r, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨t, s₂, h₂, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨sap, s₃, h₃, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨orc, s₄, h₄, hk⟩ := Parser.bind_eq_some.mp hk
  obtain ⟨iw, s₅, h₅, hk⟩ := Parser.bind_eq_some.mp hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨b, c, d⟩ := r
  obtain ⟨wt, hwt, rfl⟩ := readTransparent_writes h₂
  obtain ⟨ws, hws, rfl⟩ := readSaplingV5_writes h₃
  obtain ⟨wo, hwo, rfl⟩ := readOrchardBundle_writes h₄
  obtain ⟨wi, hwi, rfl⟩ := readOrchardBundle_writes h₅
  rw [readHeaderFragment_enc h₁]
  refine ⟨toLeBytes 4 b ++ toLeBytes 4 c ++ toLeBytes 4 d ++ wt ++ ws ++ wo ++ wi,
    fun buf => ?_, by simp only [List.append_assoc]⟩
  have hwt' := hwt ⟨v, b, c, d, t, none, sap, orc, iw⟩ rfl
  simp only [TransactionData.writeV6, TransactionData.writeV5Header, Option.isSome_none,
    Bool.false_eq_true, ite_false, bind, Except.bind, vec_write, hwt', hws,
    writeV6OrchardBundle_eq (fun h => hrev (.inl h)), writeV6OrchardBundle_eq
      (fun h => hrev (.inr h)), hwo, hwi, List.append_assoc]

/-- **A version 5 or 6 transaction `zcash_primitives` reads is written back as exactly the bytes
    it was read from**; in version 6 with an Orchard or Ironwood bundle, under a branch of the
    third Orchard protocol revision (NU6.3 or NU7), as Zebra requires of every version 6
    transaction it parses. -/
theorem write_eq_read_bytes {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : read ctx s = some (.tx tx, s'))
    (hrev : tx.version = .v6 → tx.orchardBundle.isSome ∨ tx.ironwoodBundle.isSome →
      orchardProtocolRevision tx.consensusBranchId = some .v3) :
    ∃ w, tx.write ([] : VecU8) = .ok w ∧ s = w ++ s' := by
  obtain ⟨s₁, ⟨hv, ht⟩ | ⟨hv, ht⟩⟩ := read_tx h
  · have hver := readV5_version ht
    obtain ⟨w, hw, rfl⟩ := readV5_writes ht
    refine ⟨tx.version.write ++ w, ?_, ?_⟩
    · simpa [TransactionData.write, hver] using hw []
    · rw [readTxVersion_write hv, hver, List.append_assoc]
  · have hver := readV6_version ht
    obtain ⟨w, hw, rfl⟩ := readV6_writes ht (hrev hver)
    refine ⟨tx.version.write ++ w, ?_, ?_⟩
    · simpa [TransactionData.write, hver] using hw []
    · rw [readTxVersion_write hv, hver, List.append_assoc]

/-- **Reading what `write` writes of a version 5 or 6 transaction `zcash_primitives` read gives
    the same transaction back**, whatever follows it. -/
theorem write_read {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : read ctx s = some (.tx tx, s'))
    (hrev : tx.version = .v6 → tx.orchardBundle.isSome ∨ tx.ironwoodBundle.isSome →
      orchardProtocolRevision tx.consensusBranchId = some .v3) :
    ∃ w, tx.write ([] : VecU8) = .ok w ∧ ∀ r, read ctx (w ++ r) = some (.tx tx, r) := by
  obtain ⟨w, hw, rfl⟩ := write_eq_read_bytes h hrev
  obtain ⟨w', hs, hr⟩ := consumes_read ctx _ _ _ h
  obtain rfl := List.append_cancel_right hs
  exact ⟨w, hw, hr⟩

/-- An error in a step of a writer is the writer's error. -/
theorem bind_error {α β : Type} (x : IoResult α) {f : α → IoResult β}
    (hf : ∀ a, f a = .error ()) : (x >>= f) = .error () := by
  cases x <;> simp [bind, Except.bind, hf]

/-- **Writing a version 6 transaction `zcash_primitives` read, with an Orchard bundle under NU5
    to NU6.2, fails**: `read_v6_bundle` gives the bundle the version `orchard_insecure_v1` or
    `orchard_v2`, which `write_v6_bundle` rejects. Zebra rejects such a transaction when it parses
    it, so every one it parses can be written. -/
theorem write_v6_earlier {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : read ctx s = some (.tx tx, s')) (hv : tx.version = .v6)
    (b : Orchard.Bundle) (hb : tx.orchardBundle = some b)
    (hrev : orchardProtocolRevision tx.consensusBranchId = some .insecureV1 ∨
      orchardProtocolRevision tx.consensusBranchId = some .v2) (buf : VecU8) :
    tx.write buf = .error () := by
  have hp := (read_wellFormed h).orchardPool b hb
  have hw : ∀ buf' : VecU8,
      writeV6OrchardBundle tx.consensusBranchId tx.orchardBundle buf' = .error () := by
    intro buf'
    simp only [writeV6OrchardBundle, hb, hp]
    rcases hrev with hr | hr <;>
      simp [bundleVersionForBranch, hr, checkV6BundleVersion, bind, Except.bind]
  simp only [TransactionData.write, hv, TransactionData.writeV6]
  split
  · rfl
  · exact bind_error _ fun _ => bind_error _ fun _ => bind_error _ fun _ => by rw [hw]; rfl

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Read.write_eq_read_bytes' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms write_eq_read_bytes

/--
info: 'ZcashSighash.Verifier.Read.write_read' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms write_read

/--
info: 'ZcashSighash.Verifier.Read.write_v6_earlier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms write_v6_earlier

end ZcashSighash.Verifier.Read
