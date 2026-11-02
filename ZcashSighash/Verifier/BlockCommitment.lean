/-
Zakura's commitment, in a block's header, to its transactions' auth digests: `zakura-chain`
10.0.0, `src/block/merkle.rs` (`AuthDataRoot`) and `src/block/commitment.rs`
(`hashBlockCommitments`).
-/
module

public import ZcashSighash.Verifier.Native

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes personal)
open Orchard (update finalize)

/-- `auth_data_hash` (`src/block/merkle.rs`, lines 142–156); the `expect` cannot panic: the
    hash is 32 bytes. -/
def authDataHash (h1 h2 : Blake2bHash) : Option Blake2bHash := do
  let state ← hasher (personal "ZcashAuthDatHash")
  pure (finalize (update (update state h1) h2))

/-- `AUTH_DIGEST_PLACEHOLDER` (line 311). -/
def AUTH_DIGEST_PLACEHOLDER : Blake2bHash := List.replicate 32 0xff

/-- `auth_digest_or_placeholder` (lines 314–316), given the transaction's `auth_digest`
    (`src/transaction.rs`, lines 431–440): none before version 5. -/
def authDigestOrPlaceholder (authDigest : Option Blake2bHash) : Blake2bHash :=
  authDigest.getD AUTH_DIGEST_PLACEHOLDER

/-- One pass of the loop: `hashes.chunks(2).map(...).collect()` (lines 390–396). A chunk of one
    is `unreachable!`, a panic. -/
def authDataLevel : List Blake2bHash → Option (List Blake2bHash)
  | [] => some []
  | [_] => none
  | h1 :: h2 :: rest => do pure ((← authDataHash h1 h2) :: (← authDataLevel rest))

/-- A pass halves the list; the loop's termination argument. -/
theorem authDataLevel_length {hashes next : List Blake2bHash}
    (h : authDataLevel hashes = some next) : 2 * next.length = hashes.length := by
  induction hashes using authDataLevel.induct generalizing next with
  | case1 => simp_all [authDataLevel]
  | case2 => simp [authDataLevel] at h
  | case3 h1 h2 rest ih =>
    simp only [authDataLevel, Option.pure_def, Option.bind_eq_bind] at h
    obtain ⟨d, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, hn⟩ := Option.bind_eq_some_iff.mp h
    cases hn
    have := ih hr
    simp
    omega

/-- The loop `while hashes.len() > 1` (lines 389–397), then `hashes[0]` (line 399), a panic on
    an empty list. -/
def authDataLoop (hashes : List Blake2bHash) : Option Blake2bHash :=
  if _ : hashes.length > 1 then
    match _h : authDataLevel hashes with
    | some next => authDataLoop next
    | none => none
  else hashes[0]?
termination_by hashes.length
decreasing_by have := authDataLevel_length _h; omega

/-- `AuthDataRoot::from_iter` over auth digests (lines 374–401). `next_power_of_two` gives the
    least power of two at least the length, which cannot overflow at a block's size; the
    `assert!` holds. -/
def authDataRoot (authDigests : List Blake2bHash) : Option Blake2bHash :=
  let padCount := 2 ^ Nat.clog 2 authDigests.length - authDigests.length
  authDataLoop (authDigests ++ List.replicate padCount (List.replicate 32 0))

/-- `AuthDataRoot::from_iter` over transactions (lines 318–331), given each one's
    `auth_digest`. -/
def authDataRootOfTransactions (authDigests : List (Option Blake2bHash)) :
    Option Blake2bHash :=
  authDataRoot (authDigests.map authDigestOrPlaceholder)

/-- `ChainHistoryBlockTxAuthCommitmentHash::from_commitments` (`src/block/commitment.rs`,
    lines 300–321); the `expect` cannot panic. -/
def fromCommitments (historyTreeRoot authDataRoot : Blake2bHash) : Option Blake2bHash := do
  let state ← hasher (personal "ZcashBlockCommit")
  pure (finalize (update (update (update state historyTreeRoot) authDataRoot)
    (List.replicate 32 0)))

end ZcashSighash.Verifier.Native
