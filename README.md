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
