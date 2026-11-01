/-
# Zcash transaction digests (ZIP 244, ZIP 229): verified in Lean

* `Spec.lean`: the transaction digests and signature check as ZIP 244 and ZIP 229 define them.
* `Proofs/Spec.lean`: what the specification is meant to do, checked against what it says.
* `Verifier/Blake2b.lean`: BLAKE2b (RFC 7693), with the `blake2b_simd` interface.
-/
module

public import ZcashSighash.Spec
public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Verifier.Blake2b
