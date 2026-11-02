# Formalizing Zcash transaction digests

A Zcash transaction's identifier, its authorizing-data commitment, and the digests its
signatures sign are defined by ZIP 244 (version 5) and ZIP 229 (version 6); before them, the
signature digests by ZIP 143 (version 3) and ZIP 243 (version 4). This repository states those
definitions in Lean 4, with the hash as a parameter, and proves that the Rust code that computes
them gives the specification's digests with BLAKE2b-256. Each theorem states its hypotheses:

- `zcash_primitives` 0.31.0 (librustzcash, which Zebra uses): `to_txid`, `auth_commitment` and
  `signature_hash` give the specification's digests for every version 3 to 6 transaction its
  encoding can express: no empty bundles, Sapling spends that share one anchor, Orchard and
  Ironwood bundles in their own pools, scripts no longer than `MAX_COMPACT_SIZE`, and a coin for
  each input. Outside those hypotheses, theorems state what it computes instead, or that it
  panics.
- `zakura-primitives` 4.0.0 (Zakura's fork of it): the same digests under the same hypotheses,
  for scripts of any length. Zakura's node computes version 4 to 6 signature digests, and version
  5 and 6 identifiers and auth digests, with its own code in `zakura-chain`.
- `zakura-chain` 10.0.0: for versions 5 and 6, that code gives the specification's identifiers,
  auth digests and signature digests, for transactions as it parses them: scripts that fit in a
  protocol message, a coin for each input, and no input that spends a coin with the null
  outpoint. Its version 4 signature digest is not yet proven.
- `zakura-script` 5.0.0, the callback that gives `zcash_script` 0.6.0's `OP_CHECKSIG` its digest:
  in versions 5 and 6, the specification's digest, or none where ZIP 244 says validation fails
  (an undefined hash type, or `SIGHASH_SINGLE` without a corresponding output), which fails the
  signature check; in versions 3 and 4, the digest of the signature's own hash-type byte. It never
  panics. In versions 5 and 6 it is proven with `zakura-chain`'s `SigHasher`; in versions 3 and
  4 the theorems assume the `SigHasher` computes the specification's digests.

| Crate               | Version | Status                   | Assumes                         |
|---------------------|---------|--------------------------|---------------------------------|
| `zcash_primitives`  | 0.31.0  | Proven, versions 3 to 6  | `blake2b_simd` computes BLAKE2b |
| `zakura-primitives` | 4.0.0   | Proven, versions 3 to 6  | `blake2b_simd` computes BLAKE2b |
| `zakura-script`     | 5.0.0   | Proven, versions 3 to 6  | Version 4 `SigHasher` digests   |
| `zakura-chain`      | 10.0.0  | Proven, versions 5 and 6 | `blake2b_simd` computes BLAKE2b |

The specification and both `zcash_primitives` transcriptions give the digests of ZIP 244's, ZIP
143's and ZIP 243's test vectors, and of the two version 6 transactions in the crates' own tests;
`zakura-chain`'s, those of the version 5 and 6 ones. Versions 1 and 2 sign a SHA-256d digest
neither crate computes; both panic on them. The transcribed code has no `unsafe` blocks, which
CI checks.

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

The Lean in `ZcashSighash/Verifier/` transcribes librustzcash's crates, Copyright (c) Electric
Coin Company (and, for `orchard`, Zcash Open Development Lab), and Zakura's, Copyright (c) The
Zakura Contributors, all under MIT OR Apache-2.0; and `zcash_script` 0.6.0, by the Electric
Coin Company, the Zcash Foundation and others, under Apache-2.0. The test data in
`ZcashSighash/Tests/` is copied from `zcash_primitives` 0.31.0 and `zakura-primitives` 4.0.0.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
