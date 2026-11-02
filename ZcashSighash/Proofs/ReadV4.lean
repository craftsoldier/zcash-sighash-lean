/-
What `zcash_primitives`' reader computes for a transaction of version 1 to 4: its identifier is
the SHA-256d of the bytes `Transaction::read` read, and reading those bytes again, before
anything, gives the same transaction and identifier (`read_v4_txid`).
-/
module

public import ZcashSighash.Proofs.Write

@[expose] public section

namespace ZcashSighash.Verifier.Read

open Spec (Byte Bytes)
open Native (Parser readBytes readLe fail readCount Parser.bind_eq_some pure_apply)

/-- **The identifier of a transaction of version 1 to 4 that `Transaction::read` returns is the
    SHA-256d of the bytes it read.** -/
theorem read_v4_txid {ctx : Transparent.AuthorizingContext} {bid : BitVec 32} {s s' : List Byte}
    {tx : TransactionData} {txid : List Byte} (h : read ctx bid s = some (.v4 tx txid, s')) :
    ∃ w, s = w ++ s' ∧ txid = (Sha256.sha256d (w.map (·.toNat))).map (BitVec.ofNat 8) ∧
      ∀ r, read ctx bid (w ++ r) = some (.v4 tx txid, r) := by
  obtain ⟨w, rfl, hw⟩ := consumes_read ctx bid _ _ _ h
  refine ⟨w, rfl, ?_, hw⟩
  have cv : Consumes readTxVersion := by unfold readTxVersion; consumes_tac
  obtain ⟨⟨v, hdr⟩, s₁, h₁, hk⟩ := Parser.bind_eq_some.mp h
  obtain ⟨hv, rfl⟩ := hashReader_eq_some h₁
  obtain ⟨w₁, hw₁, -⟩ := cv _ _ _ hv
  dsimp only at hk
  cases v
  case v5 =>
    cases hr : readV5 ctx .v5 s₁ <;> simp [Functor.map, StateT.map, hr] at hk
  case v6 =>
    cases hr : readV6 ctx .v6 s₁ <;> simp [Functor.map, StateT.map, hr] at hk
  all_goals
    obtain ⟨⟨data, body⟩, s₂, h₂, k₂⟩ := Parser.bind_eq_some.mp hk
    obtain ⟨hr₂, rfl⟩ := hashReader_eq_some h₂
    obtain ⟨w₂, rfl, -⟩ := consumes_readV4 ctx _ bid _ _ _ hr₂
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, ReadOutcome.v4.injEq] at k₂
    obtain ⟨⟨-, rfl⟩, rfl⟩ := k₂
    have hw : w = w₁ ++ w₂ := List.append_cancel_right (by rw [hw₁, List.append_assoc])
    subst hw
    simp [hw₁]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Read.read_v4_txid' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms read_v4_txid

end ZcashSighash.Verifier.Read
