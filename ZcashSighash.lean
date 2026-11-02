/-
# Zcash transaction digests (ZIP 143, ZIP 243, ZIP 244, ZIP 229): verified in Lean

* `Spec.lean`: the transaction digests and signature check as ZIPs 143, 243, 244 and 229 define
  them.
* `Proofs/Spec.lean`: what the specification is meant to do, checked against what it says.
* `Verifier/Blake2b.lean`: BLAKE2b (RFC 7693), with the `blake2b_simd` interface.
* `Verifier/`: librustzcash's digests, transcribed statement by statement.
* `Proofs/Verifier.lean`: the transcription computes the specification's digests.
* `Proofs/VerifierV4.lean`: the same for versions 3 and 4.
* `Proofs/Seams.lean`: what it computes outside those theorems' hypotheses.
-/
module

public import ZcashSighash.Spec
public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Proofs.Verifier
public import ZcashSighash.Proofs.Seams
public import ZcashSighash.Proofs.VerifierV4
public import ZcashSighash.Verifier.Blake2b
public import ZcashSighash.Verifier.Encoding
public import ZcashSighash.Verifier.Transparent
public import ZcashSighash.Verifier.Shielded
public import ZcashSighash.Verifier.TxId
public import ZcashSighash.Verifier.Sighash
public import ZcashSighash.Verifier.SighashV4
public import ZcashSighash.Verifier.Zakura
