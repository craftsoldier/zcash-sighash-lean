/-
# Zcash transaction digests (ZIP 143, ZIP 243, ZIP 244, ZIP 229): verified in Lean

* `Spec.lean`: the transaction digests and signature check as ZIPs 143, 243, 244 and 229 define
  them.
* `Proofs/Spec.lean`: what the specification is meant to do, checked against what it says.
* `Proofs/Commitments.lean`: what the identifier and auth digest commit to, and what they ignore.
* `Verifier/Blake2b.lean`: BLAKE2b (RFC 7693), with the `blake2b_simd` interface.
* `Verifier/`: librustzcash's digests, transcribed statement by statement.
* `Proofs/Verifier.lean`: the transcription computes the specification's digests.
* `Proofs/VerifierV4.lean`: the same for versions 3 and 4.
* `Proofs/Zakura.lean`: the same for Zakura's fork.
* `Proofs/Seams.lean`: what it computes outside those theorems' hypotheses.
* `Verifier/Script.lean`: Zakura's sighash callback and `zcash_script`'s signature check.
* `Proofs/Script.lean`: the callback gives each signature check the specification's digest.
* `Verifier/Native.lean`: Zakura's own digests, which its node validates blocks with.
* `Proofs/Native.lean`: they compute the specification's digests, for versions 5 and 6.
* `Verifier/NativeV4.lean`: Zakura's own version 4 signature digest.
* `Proofs/NativeV4.lean`: it computes the specification's digest.
* `Verifier/BlockCommitment.lean`: Zakura's commitment to a block's auth digests.
* `Proofs/BlockCommitment.lean`: it is the specification's.
* `Verifier/PushNum.lean`: `zcash_script`'s `push_num`, which encodes a coinbase input's height.
* `Verifier/Parse.lean`: Zakura's parser for transparent inputs and outputs.
* `Proofs/Parse.lean`: what it parses meets the native theorems' hypotheses.
* `Verifier/Read.lean`: librustzcash's reader, for every version.
* `Proofs/Read.lean`: every version 5 and 6 transaction it reads meets the digest theorems'
  hypotheses, and its values are in range.
* `Verifier/Write.lean`: librustzcash's writer, for every version.
* `Proofs/Write.lean`: it writes back the bytes the reader read of a version 5 and 6 transaction,
  and the reader reads them back.
* `Verifier/Sha256.lean`: SHA-256 (FIPS 180-4), which a version 1 to 4 identifier is made of.
* `Proofs/ReadV4.lean`: that identifier is the SHA-256d of the bytes the reader read.
* `Verifier/Zebra.lean`: Zebra's signature digests, of the transaction rebuilt.
* `Proofs/Zebra.lean`: for a version 5 or 6 transaction the reader returns, under its own branch
  ID, and coins that fit it, they are the specification's.
-/
module

public import ZcashSighash.Spec
public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Proofs.Commitments
public import ZcashSighash.Proofs.Verifier
public import ZcashSighash.Proofs.Seams
public import ZcashSighash.Proofs.VerifierV4
public import ZcashSighash.Proofs.Zakura
public import ZcashSighash.Proofs.Script
public import ZcashSighash.Proofs.Native
public import ZcashSighash.Proofs.NativeV4
public import ZcashSighash.Proofs.BlockCommitment
public import ZcashSighash.Proofs.Parse
public import ZcashSighash.Proofs.Read
public import ZcashSighash.Proofs.Zebra
public import ZcashSighash.Proofs.Write
public import ZcashSighash.Proofs.ReadV4
public import ZcashSighash.Verifier.Blake2b
public import ZcashSighash.Verifier.Encoding
public import ZcashSighash.Verifier.Transparent
public import ZcashSighash.Verifier.Shielded
public import ZcashSighash.Verifier.TxId
public import ZcashSighash.Verifier.Sighash
public import ZcashSighash.Verifier.SighashV4
public import ZcashSighash.Verifier.Zakura
public import ZcashSighash.Verifier.Script
public import ZcashSighash.Verifier.Native
public import ZcashSighash.Verifier.NativeV4
public import ZcashSighash.Verifier.BlockCommitment
public import ZcashSighash.Verifier.PushNum
public import ZcashSighash.Verifier.Parse
public import ZcashSighash.Verifier.Read
public import ZcashSighash.Verifier.Zebra
public import ZcashSighash.Verifier.Write
public import ZcashSighash.Verifier.Sha256
