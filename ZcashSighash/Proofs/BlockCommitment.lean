/-
Zakura's commitment to a block's auth digests (`hashAuthDataRoot`) and its block commitments hash
are the specification's (ZIP 244, Block Header Changes). Zakura builds the tree bottom up, a
level at a time; the specification states it top down, by halves.
-/
module

public import ZcashSighash.Proofs.Native
public import ZcashSighash.Verifier.BlockCommitment

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes Digest personal)
open Orchard (update finalize)

/-- `auth_data_hash` is the specification's non-leaf hash. -/
theorem authDataHash_eq (a b : Digest) :
    authDataHash a.toList b.toList =
      some (Spec.node blake2b256 (personal "ZcashAuthDatHash") [a, b]).toList := by
  simp [authDataHash, hasher_eq, update_absorbed, finalize_state_absorbed, Spec.node]

/-- `from_commitments` is the specification's `hashBlockCommitments`. -/
theorem fromCommitments_eq (lightClientRoot authDataRoot : Digest) :
    fromCommitments lightClientRoot.toList authDataRoot.toList =
      some (Spec.hashBlockCommitments blake2b256 lightClientRoot authDataRoot).toList := by
  simp [fromCommitments, hasher_eq, update_absorbed, finalize_state_absorbed,
    Spec.hashBlockCommitments, Spec.node, Spec.nullDigest]

/-- One level of the tree, as the specification's nodes: each pair of nodes hashed. -/
def specLevel : List Digest → List Digest
  | a :: b :: rest => Spec.node blake2b256 (personal "ZcashAuthDatHash") [a, b] :: specLevel rest
  | _ => []

/-- On an even number of nodes, a pass of Zakura's loop is a level of the tree. -/
theorem authDataLevel_eq (l : List Digest) (h : l.length % 2 = 0) :
    authDataLevel (l.map (·.toList)) = some ((specLevel l).map (·.toList)) := by
  induction l using specLevel.induct with
  | case1 a b rest ih =>
    simp at h
    simp [authDataLevel, specLevel, authDataHash_eq, ih (by omega)]
  | case2 l hl =>
    match l, hl with
    | [], _ => rfl
    | [_], _ => simp at h
    | _ :: _ :: _, hl => exact absurd rfl (hl _ _ _)

/-- The first `n` nodes of a level are the level of the first `2 * n` nodes. -/
theorem take_specLevel (n : ℕ) (l : List Digest) :
    (specLevel l).take n = specLevel (l.take (2 * n)) := by
  induction l using specLevel.induct generalizing n with
  | case1 a b rest ih =>
    cases n with
    | zero => simp [specLevel]
    | succ n => simp [specLevel, Nat.mul_succ, ih]
  | case2 l hl =>
    match l, hl with
    | [], _ => simp [specLevel]
    | [_], _ => cases n <;> simp [specLevel, Nat.mul_succ]
    | _ :: _ :: _, hl => exact absurd rfl (hl _ _ _)

/-- The nodes of a level after the first `n` are the level of the nodes after the first
    `2 * n`. -/
theorem drop_specLevel (n : ℕ) (l : List Digest) :
    (specLevel l).drop n = specLevel (l.drop (2 * n)) := by
  induction l using specLevel.induct generalizing n with
  | case1 a b rest ih =>
    cases n with
    | zero => simp
    | succ n => simp [specLevel, Nat.mul_succ, ih]
  | case2 l hl =>
    match l, hl with
    | [], _ => simp [specLevel]
    | [_], _ => cases n <;> simp [specLevel, Nat.mul_succ]
    | _ :: _ :: _, hl => exact absurd rfl (hl _ _ _)

/-- The tree of height `h` over a level of `2 ^ (h + 1)` nodes is the tree of height `h + 1`
    over the nodes. -/
theorem authDataTree_specLevel (h : ℕ) (l : List Digest) (hl : l.length = 2 ^ (h + 1)) :
    Spec.authDataTree blake2b256 h (specLevel l) = Spec.authDataTree blake2b256 (h + 1) l := by
  induction h generalizing l with
  | zero =>
    match l, hl with
    | [_, _], _ => rfl
  | succ h ih =>
    rw [Spec.authDataTree, take_specLevel, drop_specLevel, ← pow_succ',
      ih _ (by simp [hl, pow_succ]; omega), ih _ (by simp [hl, pow_succ]; omega)]
    rfl

/-- On `2 ^ h` leaves, Zakura's loop gives the root of the tree of height `h`. -/
theorem authDataLoop_eq (h : ℕ) (l : List Digest) (hl : l.length = 2 ^ h) :
    authDataLoop (l.map (·.toList)) = some (Spec.authDataTree blake2b256 h l).toList := by
  induction h generalizing l with
  | zero =>
    match l, hl with
    | [a], _ => simp [authDataLoop, Spec.authDataTree]
  | succ h ih =>
    have hgt : (l.map (·.toList)).length > 1 := by simp [hl]
    have hlev := authDataLevel_eq l (by rw [hl, pow_succ]; omega)
    have hlen : (specLevel l).length = 2 ^ h := by
      have := authDataLevel_length hlev
      simp at this; rw [hl, pow_succ] at this; omega
    rw [authDataLoop]
    split
    · split
      · rename_i next hn
        rw [hlev] at hn
        cases hn
        rw [ih _ hlen, authDataTree_specLevel h l hl]
      · rename_i hn
        simp [hlev] at hn
    · contradiction

/-- **Zakura's `hashAuthDataRoot` is the specification's**, for any number of auth digests. -/
theorem authDataRoot_eq (leaves : List Digest) :
    authDataRoot (leaves.map (·.toList)) =
      some (Spec.hashAuthDataRoot blake2b256 leaves).toList := by
  have hle := Nat.le_pow_clog (b := 2) (by omega) leaves.length
  have hpad : leaves.map (·.toList) ++ List.replicate
      (2 ^ Nat.clog 2 leaves.length - leaves.length) (List.replicate 32 (0 : Byte)) =
      (leaves ++ List.replicate (2 ^ Nat.clog 2 leaves.length - leaves.length)
        Spec.nullDigest).map (·.toList) := by
    simp [Spec.nullDigest]
  simp only [authDataRoot, List.length_map, hpad]
  exact authDataLoop_eq _ _ (by simp; omega)

/-- **Zakura's `hashAuthDataRoot` of a block's transactions is the specification's**: each
    transaction's auth digest, or the placeholder before version 5, as the leaves. -/
theorem authDataRootOfTransactions_eq (authDigests : List (Option Digest)) :
    authDataRootOfTransactions (authDigests.map (Option.map (·.toList))) =
      some (Spec.hashAuthDataRoot blake2b256 (authDigests.map Spec.authDataLeaf)).toList := by
  have : (authDigests.map (Option.map (·.toList))).map authDigestOrPlaceholder =
      (authDigests.map Spec.authDataLeaf).map (·.toList) := by
    simp only [List.map_map]
    congr 1
    funext d
    cases d <;> simp [authDigestOrPlaceholder, Spec.authDataLeaf, AUTH_DIGEST_PLACEHOLDER]
  simp only [authDataRootOfTransactions, this, authDataRoot_eq]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Native.authDataRootOfTransactions_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms authDataRootOfTransactions_eq

/--
info: 'ZcashSighash.Verifier.Native.fromCommitments_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fromCommitments_eq

end ZcashSighash.Verifier.Native
