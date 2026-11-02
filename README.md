# Formalizing Zcash transaction digests

A Zcash transaction's identifier and the digests its signatures sign are defined by ZIP 244
(version 5) and ZIP 229 (version 6). This repository states those definitions in Lean 4
(`ZcashSighash/Spec.lean`), proves what they are meant to guarantee
(`ZcashSighash/Proofs/Spec.lean`), and will prove that librustzcash computes them.

The specification takes the hash as a parameter: it holds for every hash function, and its
theorems say when they need one without collisions. BLAKE2b enters only through
`ZcashSighash/Verifier/Blake2b.lean`, checked on RFC 7693's test vector. With it, the
specification gives the identifier, auth digest and signature digests of each of ZIP 244's ten
test vectors, and the digests the crates' tests give for two version 6 transactions
(`ZcashSighash/Tests/Spec.lean`). The specification's sources are in `spec/`,
copied verbatim from the ZIPs with a header naming their commit.

`ZcashSighash/Verifier/` transcribes, statement by statement, the code that computes these
digests in `zcash_primitives` 0.31.0 and the crates it calls (`zcash_transparent` 0.11.0,
`zcash_encoding` 0.5.0, `orchard` 0.16.0, `sapling-crypto` 0.9.0); each definition cites the
lines it transcribes, and CI checks each crate against its crates.io checksum. The transcription
gives the same twelve transactions' digests (`ZcashSighash/Tests/Verifier.lean`).

`ZcashSighash/Proofs/Verifier.lean` proves that, with BLAKE2b-256, the transcription computes
the specification's digests for every version 5 and 6 transaction: `txid_eq` (`to_txid`),
`authCommitment_eq` (`auth_commitment`) and `signatureHash_eq`
(`PrecomputedSighashData::signature_hash`, with `newZip244_eq`). Their hypotheses, `WellFormed`
and `ContextFits`, name what the Rust types allow and a transaction read from its encoding never
has: an empty transparent or Sapling bundle, Sapling spends with different anchors, an Orchard
or Ironwood bundle in the other's pool, a script longer than `MAX_COMPACT_SIZE`, and an
authorizing context without one entry per input. A signed transparent input must carry a hash
type `SighashType::parse` accepts and its coin's value and `scriptPubKey`.

## Verifying the proofs

A successful build is the verification: building re-checks every proof. Install
[elan](https://github.com/leanprover/elan), which reads `lean-toolchain` and installs the
pinned Lean version, then from the repository root:

    lake exe cache get   # one-time: download prebuilt Mathlib
    lake build --wfail   # check every proof; warnings fail, as in CI

## License

Copyright 2026 Julian Abraham (craftsoldier).

All code in this workspace is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

The ZIP excerpts in `spec/` are under the MIT license in [`spec/COPYING.rst`](spec/COPYING.rst).
