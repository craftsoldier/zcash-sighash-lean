/-
What the transcribed `zcash_primitives` does outside the hypotheses of `Proofs/Verifier.lean`:
each hypothesis rules out an input on which the Rust computes something other than the
specification's digest, or panics.
-/
module

public import ZcashSighash.Proofs.Verifier

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)

/-- An empty transparent bundle, which `Transaction::read` never builds (it reads none), is
    hashed as three empty digests, where the specification hashes nothing (§T.2). -/
theorem hashTransparentTxidData_empty (b : Transparent.Bundle) (hi : b.vin = [])
    (ho : b.vout = []) :
    hashTransparentTxidData (some (txidDigestsOf b)) =
      some (blake2b256 (personal "ZTxIdTranspaHash")
        ((blake2b256 (personal "ZTxIdPrevoutHash") []).toList ++
          (blake2b256 (personal "ZTxIdSequencHash") []).toList ++
          (blake2b256 (personal "ZTxIdOutputsHash") []).toList)).toList ∧
    Spec.transparentDigest blake2b256 b.toSpec = blake2b256 (personal "ZTxIdTranspaHash") [] := by
  constructor
  · simp [hashTransparentTxidData, txidDigestsOf, hasher_eq, writeAll_absorbed, unwrap_ok,
      finalize_absorbed, Spec.prevoutsDigest, Spec.sequenceDigest, Spec.outputsDigest,
      Transparent.Bundle.toSpec, hi, ho, bind]
  · simp [Spec.transparentDigest, Transparent.Bundle.toSpec, hi, ho]

/-- `SighashType::from_raw` keeps any byte. An undefined one, such as `0x41`, which
    `SighashType::parse` and the specification reject, sets none of the flags
    `transparent_sig_digest` tests: it is hashed as `SIGHASH_ALL`, under its own byte. -/
theorem undefined_hashType_as_all :
    Transparent.SighashType.parse 0x41 = none ∧ Spec.HashType.ofByte? 0x41 = none ∧
    ((0x41 : Byte) &&& Transparent.SIGHASH_ANYONECANPAY != 0) = false ∧
    ((0x41 : Byte) &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_SINGLE) = false ∧
    ((0x41 : Byte) &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_NONE) = false := by
  decide

/-- A script longer than `MAX_COMPACT_SIZE` cannot be written, so every digest that writes one
    panics; the specification's digests are defined for it. -/
theorem script_write_long (s : Transparent.Script) (hs : MAX_COMPACT_SIZE < s.code.length)
    (w : StateWrite) : s.write w = .error () := by
  simp [Transparent.Script.write, Vector.write, CompactSize.write, hs, bind, Except.bind]

/-- For example, `transparent_outputs_hash` panics on an output whose script is longer than
    `MAX_COMPACT_SIZE`. -/
theorem transparentOutputsHash_long (o : Transparent.TxOut)
    (hs : MAX_COMPACT_SIZE < o.scriptPubkey.code.length) :
    transparentOutputsHash [o] = none := by
  simp [transparentOutputsHash, hasher_eq, Transparent.TxOut.write, classWrite_absorbed,
    script_write_long _ hs, unwrap, bind, Except.bind]

/-- An Ironwood bundle in a version 5 transaction's Orchard slot panics. -/
theorem digestOrchard_ironwood_v5 (b : Orchard.Bundle) (hp : b.valuePool = .ironwood) :
    TxIdDigester.digestOrchard .v5 (some b) = none := by
  simp [TxIdDigester.digestOrchard, orchardCommitmentDomain, Orchard.hashBundleTxidData, hp,
    Orchard.ValuePool.commitmentFormat, unwrap]

/-- An Ironwood bundle in a version 6 transaction's Orchard slot is hashed with Ironwood's
    personalizations: the digest is the bundle's pool's, not its slot's. -/
theorem digestOrchard_ironwood_v6 (b : Orchard.Bundle) (hp : b.valuePool = .ironwood) :
    TxIdDigester.digestOrchard .v6 (some b) =
      some (some (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList) := by
  simp [TxIdDigester.digestOrchard, orchardCommitmentDomain, hashBundleTxidData_ironwoodV6 b hp,
    unwrap_ok]

/-- In version 5 each Sapling spend's own anchor is hashed (§T.3a.ii holds one anchor for all
    of them: the encoding has one). -/
theorem hashSaplingSpends_v5 (spends : List Sapling.SpendDescription) (hs : spends ≠ []) :
    hashSaplingSpends .v5 spends = some (blake2b256 (personal "ZTxIdSSpendsHash")
      ((blake2b256 (personal "ZTxIdSSpendCHash") (spends.flatMap (·.nullifier.toList))).toList ++
        (blake2b256 (personal "ZTxIdSSpendNHash")
          (spends.flatMap fun s =>
            s.cv.toList ++ s.anchor.toList ++ s.rk.toList)).toList)).toList := by
  simp only [hashSaplingSpends, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [ite_eq_left (by simpa using hs)]
  rw [forIn_yield _ _ _ (fun (s : Sapling.SpendDescription) st =>
    (st.1.append s.nullifier.toList,
      st.2.append (s.cv.toList ++ s.anchor.toList ++ s.rk.toList)))
    (fun a _ st => by simp [writeAll_eq, unwrap_ok, append_append])]
  rw [foldl_prod _ _ _ (fun (s : StateWrite) (a : Sapling.SpendDescription) =>
      s.append a.nullifier.toList)
    (fun (s : StateWrite) (a : Sapling.SpendDescription) =>
      s.append (a.cv.toList ++ a.anchor.toList ++ a.rk.toList)),
    foldl_append_absorbed, foldl_append_absorbed]
  simp [writeAll_absorbed, unwrap_ok, finalize_absorbed, saplingSpendsNoncompactPersonalization]

end ZcashSighash.Verifier
