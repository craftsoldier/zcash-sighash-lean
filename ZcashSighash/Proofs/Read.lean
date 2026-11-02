/-
What `zcash_primitives`' reader guarantees (G3): every version 5 and 6 transaction it reads is
`WellFormed`, the hypothesis of the digest theorems (`Proofs/Verifier.lean`). So its identifier
is the specification's, and computing it, which `Transaction::read` does at once
(`from_data_v5`), never panics: the shape of GHSA-qp6f.
-/
module

public import ZcashSighash.Proofs.Parse
public import ZcashSighash.Verifier.Read

@[expose] public section

namespace ZcashSighash.Verifier.Read

open Spec (Byte Bytes)
open Native (Parser readBytes readLe fail readCount Parser.bind_eq_some pure_apply)

/-- A `CompactSize` is at most `MAX_COMPACT_SIZE`. -/
theorem readCompactSize_le {n : ℕ} {s s' : List Byte}
    (h : readCompactSize s = some (n, s')) : n ≤ MAX_COMPACT_SIZE := by
  obtain ⟨m, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  split at h
  · simp at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    omega

/-- A loop of `n` reads reads `n` elements. -/
theorem readCount_length {α : Type} {read : Parser α} :
    ∀ {n : ℕ} {s s' : List Byte} {as : List α}, readCount read n s = some (as, s') →
      as.length = n := by
  intro n
  induction n with
  | zero =>
    intro s s' as h
    change (pure [] : Parser (List α)) s = some (as, s') at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | succ n ih =>
    intro s s' as h
    obtain ⟨a, s₁, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨as', s₂, has, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [ih has]

/-- A script read has at most `MAX_COMPACT_SIZE` bytes. -/
theorem readScript_le {s s' : List Byte} {script : Transparent.Script}
    (h : readScript s = some (script, s')) : script.code.length ≤ MAX_COMPACT_SIZE := by
  obtain ⟨bytes, s₁, hb, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨n, s₂, hn, hb⟩ := Parser.bind_eq_some.mp hb
  rw [readCount_length hb]
  exact readCompactSize_le hn

/-- An input read has a `scriptSig` of at most `MAX_COMPACT_SIZE` bytes. -/
theorem readTxIn_le {s s' : List Byte} {i : Transparent.TxIn}
    (h : readTxIn s = some (i, s')) : i.scriptSig.code.length ≤ MAX_COMPACT_SIZE := by
  obtain ⟨_, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨sc, s₂, hs, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨_, s₃, -, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact readScript_le hs

/-- An output read has a script of at most `MAX_COMPACT_SIZE` bytes. -/
theorem readTxOut_le {s s' : List Byte} {o : Transparent.TxOut}
    (h : readTxOut s = some (o, s')) : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := by
  obtain ⟨v, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨sc, s₂, hs, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact readScript_le hs

/-- A `Vector::read`'s elements each meet what their reader guarantees. -/
theorem readVector_forall {α : Type} {read : Parser α} {P : α → Prop}
    (hr : ∀ s s' a, read s = some (a, s') → P a) {s s' : List Byte} {as : List α}
    (h : readVector read s = some (as, s')) : ∀ a ∈ as, P a := by
  obtain ⟨n, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  exact Native.readCount_forall hr n s₁ s' as h

/-- A transparent bundle read is not empty, and its scripts fit a `CompactSize`. -/
theorem readTransparent_spec {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {ob : Option Transparent.Bundle} (h : readTransparent ctx s = some (ob, s')) (b)
    (hb : ob = some b) : (b.vin ≠ [] ∨ b.vout ≠ []) ∧
      (∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) ∧
      ∀ i ∈ b.vin, i.scriptSig.code.length ≤ MAX_COMPACT_SIZE := by
  obtain ⟨vin, s₁, hi, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨vout, s₂, ho, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  by_cases he : vin.isEmpty && vout.isEmpty
  · simp [he] at hb
  · simp only [he, Bool.false_eq_true, ite_false, Option.some.injEq] at hb
    subst hb
    simp only [Bool.and_eq_true, List.isEmpty_iff, not_and] at he
    refine ⟨if hv : vin = [] then Or.inr (he hv) else Or.inl hv,
      readVector_forall (fun _ _ _ h => readTxOut_le h) ho,
      readVector_forall (fun _ _ _ h => readTxIn_le h) hi⟩

/-- A Sapling bundle read has a Spend or an Output, and its Spends share one anchor. -/
theorem readSaplingV5_spec {s s' : List Byte} {ob : Option Sapling.Bundle}
    (h : readSaplingV5 s = some (ob, s')) (b) (hb : ob = some b) :
    (b.shieldedSpends ≠ [] ∨ b.shieldedOutputs ≠ []) ∧
      ∀ sp ∈ b.shieldedSpends, ∀ sp' ∈ b.shieldedSpends, sp.anchor = sp'.anchor := by
  obtain ⟨sds, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨ods, s₂, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨vb, s₃, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨anchor, s₄, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨_, s₅, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨_, s₆, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨_, s₇, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨bindingSig, s₈, -, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  cases bindingSig with
  | none => simp at hb
  | some sig =>
    simp only [Option.bind_some, saplingFromParts] at hb
    split at hb
    · simp at hb
    · rename_i hne
      simp only [Option.some.injEq] at hb
      subst hb
      simp only [Bool.and_eq_true, List.isEmpty_iff, not_and] at hne
      refine ⟨by dsimp only; tauto, ?_⟩
      intro sp hsp sp' hsp'
      simp only [List.mem_map] at hsp hsp'
      obtain ⟨_, -, rfl⟩ := hsp
      obtain ⟨_, -, rfl⟩ := hsp'
      rfl

/-- An Orchard-shaped bundle read is of the value pool of its slot. -/
theorem readOrchardBundle_pool {pool : Orchard.ValuePool} {s s' : List Byte}
    {ob : Option Orchard.Bundle} (h : readOrchardBundle pool s = some (ob, s')) (b)
    (hb : ob = some b) : b.valuePool = pool := by
  obtain ⟨acts, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp at hb
  · obtain ⟨_, s₂, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨_, s₃, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨_, s₄, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨_, s₅, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨_, s₆, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨_, s₇, -, h⟩ := Parser.bind_eq_some.mp h
    dsimp only at h
    generalize nonEmptyFromVec _ = o at h
    cases o with
    | none => simp only [Native.fail_apply] at h; cases h
    | some actions =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Option.some.injEq] at hb
      rw [← hb]

/-- **Every version 5 transaction `zcash_primitives` reads is `WellFormed`**: the digest
    theorems' hypothesis holds of what parsing returns. -/
theorem readV5_wellFormed {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : readV5 ctx s = some (tx, s')) : WellFormed tx := by
  obtain ⟨_, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨t, s₂, ht, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨sap, s₃, hs, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨orc, s₄, ho, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨Or.inl rfl, fun b hb => (readTransparent_spec ht b hb).1,
    fun b hb => (readTransparent_spec ht b hb).2.1, fun b hb => (readSaplingV5_spec hs b hb).2,
    fun b hb => readOrchardBundle_pool ho b hb, fun b hb => (by cases hb),
    fun b hb => (readTransparent_spec ht b hb).2.2, fun b hb => (readSaplingV5_spec hs b hb).1⟩

/-- **Every version 6 transaction `zcash_primitives` reads is `WellFormed`.** -/
theorem readV6_wellFormed {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : readV6 ctx s = some (tx, s')) : WellFormed tx := by
  obtain ⟨_, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨t, s₂, ht, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨sap, s₃, hs, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨orc, s₄, ho, h⟩ := Parser.bind_eq_some.mp h
  obtain ⟨iw, s₅, hi, h⟩ := Parser.bind_eq_some.mp h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨Or.inr rfl, fun b hb => (readTransparent_spec ht b hb).1,
    fun b hb => (readTransparent_spec ht b hb).2.1, fun b hb => (readSaplingV5_spec hs b hb).2,
    fun b hb => readOrchardBundle_pool ho b hb, fun b hb => readOrchardBundle_pool hi b hb,
    fun b hb => (readTransparent_spec ht b hb).2.2, fun b hb => (readSaplingV5_spec hs b hb).1⟩

/-- **The identifier of every version 5 or 6 transaction `zcash_primitives` reads is the
    specification's**, so computing it as `Transaction::read` does (`from_data_v5`,
    `from_data_v6`) never panics: what GHSA-qp6f did to Zebra cannot happen here. -/
theorem read_txid_eq {ctx : Transparent.AuthorizingContext} {s s' : List Byte}
    {tx : TransactionData} (h : readV5 ctx s = some (tx, s') ∨ readV6 ctx s = some (tx, s')) :
    tx.txIdDigests.bind (toTxid tx.version tx.consensusBranchId) =
      some (some (tx.toSpec.txid blake2b256).toList) :=
  txid_eq tx (h.elim readV5_wellFormed readV6_wellFormed)

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Read.read_txid_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms read_txid_eq

end ZcashSighash.Verifier.Read
