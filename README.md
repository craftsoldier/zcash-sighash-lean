# Formalizing Zcash transaction digests

A Zcash transaction's identifier, its authorizing-data commitment, and the digests its
signatures sign are defined by ZIP 244 (version 5) and ZIP 229 (version 6); before them, the
signature digests by ZIP 143 (version 3) and ZIP 243 (version 4). This repository states those
definitions in Lean 4, with the hash as a parameter, and proves that the Rust code that computes
them gives the specification's digests with BLAKE2b-256. Each theorem states its hypotheses:

- `zcash_primitives` 0.31.0 (librustzcash, which Zebra uses): for every transaction its encoding
  can express, given no empty bundles, Sapling spends that share one anchor, Orchard and Ironwood
  bundles in their own pools, scripts no longer than `MAX_COMPACT_SIZE`, and a coin for each
  input, `signature_hash` gives the specification's digests in versions 3 to 6, and `to_txid` and
  `auth_commitment` in versions 5 and 6. A version 3 or 4 transaction's identifier is the SHA-256d
  of its encoding, which is not covered yet, and ZIP 244 puts a placeholder where its auth
  commitment would be. Every version 5 and 6 transaction its reader (`Transaction::read`) returns
  meets all but the last, which the coins looked up for it must meet, and has the version its
  first 8 bytes encode, so its digests follow that version's rules; computing its identifier,
  which the reader does at once, never panics. Zebra 7.0.0 parses every transaction with this
  reader, adding rejections of its own (`zebra-chain` 15.0.0), so this holds of every version 5
  and 6 transaction Zebra accepts. Outside those hypotheses, theorems state what it computes
  instead, or that it panics.
- `zebra-chain` 15.0.0 (Zebra 7.0.0's): its `sighash` hashes a rebuild of the transaction, with
  the consensus branch ID of the network upgrade it validates under and the coins its inputs
  spend as their authorization. For a version 5 or 6 transaction the reader returns, a network
  upgrade with another branch ID is an error; under one with its own, the rebuild changes
  nothing else, and given a coin per input (none for a coinbase, as Zebra looks up), each script
  at most `MAX_COMPACT_SIZE` bytes, `sighash` gives the specification's digests of the
  transaction spending those coins. Its version 3 and 4 digests, under the network upgrade's
  branch ID, are tested on ZIP 143's and ZIP 243's vectors, not proven.
- `zakura-primitives` 4.0.0 (Zakura's fork of it): the same digests under the same hypotheses,
  for scripts of any length. Zakura's node computes version 4 to 6 signature digests, and version
  5 and 6 identifiers and auth digests, with its own code in `zakura-chain`.
- `zakura-chain` 10.0.0: that code gives the specification's digests, for transactions as it
  parses them: scripts that fit in a protocol message, a coin for each input, and, in versions
  5 and 6, no input that spends a coin with the null outpoint. That its parser for transparent
  inputs and outputs returns only such inputs and outputs, with each coinbase `scriptSig`
  rebuilt as it was read, is proven, through `zcash_script` 0.6.0's `push_num`, which encodes
  the heights. Its block header's commitment to the transactions' auth digests
  (`hashAuthDataRoot`, and `hashBlockCommitments` over it) is ZIP 244's, for any number of
  transactions.
- `zakura-script` 5.0.0, the callback that gives `zcash_script` 0.6.0's `OP_CHECKSIG` its digest:
  in versions 5 and 6, the specification's digest, or none where ZIP 244 says validation fails
  (an undefined hash type, or `SIGHASH_SINGLE` without a corresponding output), which fails the
  signature check; in versions 3 and 4, the digest of the signature's own hash-type byte. In
  versions 4 to 6 this is proven with `zakura-chain`'s `SigHasher`, and it never panics; in
  version 3 the `SigHasher` hands the transaction to `zakura-primitives` through a wrapper
  (`src/primitives/zcash_primitives.rs`), and the theorems assume it gives that crate's digest.
  Building the `SigHasher` also converts the transaction to `zakura-primitives`' form, and Zakura
  rejects a transaction whose conversion fails; the theorems are about the digests once it is
  built.

| Crate               | Version | Status (versions)           | Assumes                         |
|---------------------|---------|-----------------------------|---------------------------------|
| `zcash_primitives`  | 0.31.0  | Proven, 3 to 6 (txid: 5, 6) | `blake2b_simd` computes BLAKE2b |
| `zakura-primitives` | 4.0.0   | Proven, 3 to 6 (txid: 5, 6) | `blake2b_simd` computes BLAKE2b |
| `zakura-script`     | 5.0.0   | Proven, 3 to 6              | Version 3 `SigHasher` digests   |
| `zakura-chain`      | 10.0.0  | Proven, 4 to 6 (txid: 5, 6) | `blake2b_simd` computes BLAKE2b |
| `zebra-chain`       | 15.0.0  | Proven, 5 and 6 (sighash)   | `blake2b_simd` computes BLAKE2b |

The specification and both `zcash_primitives` transcriptions give the digests of ZIP 244's, ZIP
143's and ZIP 243's test vectors, and of the version 5 and two version 6 transactions in the
crates' own tests; `zakura-chain`'s, those of the version 4 to 6 ones; `zebra-chain`'s, the
signature digests of all three ZIPs' and of the NU7 ones its own test uses. Versions 1 and 2 sign a
SHA-256d digest that none of these crates computes: `zcash_primitives` and `zakura-primitives`
panic on them, and `zakura-chain` hands them to `zakura-primitives`. The transcribed code has no
`unsafe` blocks, which CI checks. The theorems are about what the code computes, not what it
costs: that a block's signature digests take time linear in its size, which ZIP 143 and ZIP 244
set out to ensure, is not proven.

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
Zakura Contributors, all under MIT OR Apache-2.0; `zcash_script` 0.6.0, by the Electric Coin
Company, the Zcash Foundation and others, under Apache-2.0; `zebra-chain` 15.0.0, by the Zcash
Foundation, under MIT OR Apache-2.0; and `bounded-vec` 0.9.0, under CC0-1.0. The test data in
`ZcashSighash/Tests/` is copied from `zcash_primitives` 0.31.0, `zakura-primitives` 4.0.0,
`zakura-chain` 10.0.0 and `zebra-chain` 15.0.0.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
