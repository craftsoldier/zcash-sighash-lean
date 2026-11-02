/-
Zakura's sighash callback gives each `OP_CHECKSIG` the specification's digest, or none where
§S.2a says validation fails, and never panics doing so. Every 2026 consensus split in this area
(Zebra's GHSA-8m29, GHSA-gq4h, GHSA-cwfq and GHSA-pvmv) was in such a callback, not in the digest
code.

The callback's `SigHasher` is a parameter: the theorems assume it gives the specification's digest
for each call the callback makes, and the callback makes no other.
-/
module

public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Verifier.Script

@[expose] public section

namespace ZcashSighash.Verifier.Script

open Spec (Byte)

/-- A signature's hash-type byte, as `HashType::from_bits` keeps it: never an error under the
    consensus flags. -/
theorem fromBits_byte (b : Byte) :
    HashType.fromBits (b.setWidth 32) false = .ok
      { signedOutputs := if (b.setWidth 32 : BitVec 32) &&& 0x1f == 2 then .none
          else if (b.setWidth 32 : BitVec 32) &&& 0x1f == 3 then .single else .all
        anyoneCanPay := (b.setWidth 32 : BitVec 32) &&& 0x80 != 0
        rawBits := b.setWidth 32 } := rfl

/-- Zakura's flags for a hash type of the specification. -/
def zHashType (h : Spec.HashType) : ZHashType := h.toByte.setWidth 32

/-- `parse_zip244_hash_type` accepts exactly the bytes the specification defines (§S.2a), as the
    specification's hash types. -/
theorem parseZip244HashType_byte (b : Byte) :
    parseZip244HashType (b.setWidth 32) = (Spec.HashType.ofByte? b).map zHashType := by
  revert b
  decide

/-- Zakura's `SIGHASH_SINGLE` test is the specification's. -/
theorem single_zHashType (h : Spec.HashType) :
    (zHashType h == SINGLE || zHashType h == SINGLE_ANYONECANPAY) = (h.base == .single) := by
  rcases h with ⟨_ | _ | _, _ | _⟩ <;> decide

section
variable (H : Spec.Hash) (v : Spec.Version) (br : BitVec 32) (hd sp od : Spec.Digest)
  {t : Spec.Transparent}

/-- **The callback is §S's signature check, for versions 5 and 6.** For a signature whose
    hash-type byte is `b`, the callback returns the specification's `transparentSighash?`: the
    digest of the input under the hash type `b` encodes, or none where §S.2a says validation fails
    (an undefined hash type, or `SIGHASH_SINGLE` without a corresponding output). It never panics:
    it calls `sighash` only with a defined hash type that satisfies §S.2a, and assumes nothing of
    other calls. -/
theorem calculateSighash_v5 (sigHasher : SigHasher) (version : ℕ) (hv : 5 ≤ version)
    (outputsLen : ℕ) (hout : outputsLen = t.vout.length) (i : Fin t.vin.length)
    (scriptCode : List Byte)
    (hsh : ∀ ht : Spec.HashType, (ht.base = .single → i.val < t.vout.length) →
      sigHasher.sighash (zHashType ht) (some (i.val, scriptCode)) =
        some (Spec.signatureDigest H v br hd sp od (.transparent ht i)).toList)
    (b : Byte) (hashType : HashType) (hb : hashType.rawBits = b.setWidth 32) :
    calculateSighash sigHasher version outputsLen i.val scriptCode hashType =
      some ((Spec.transparentSighash? H v br hd sp od i b).map (·.toList)) := by
  have hv' : ¬version < 5 := by omega
  simp only [calculateSighash, hv', ite_false, hb, parseZip244HashType_byte]
  cases hb' : Spec.HashType.ofByte? b with
  | none => simp [Spec.transparentSighash?, hb']
  | some ht =>
    simp only [Option.map_some, single_zHashType]
    by_cases hs : ht.base = .single
    · by_cases hi : i.val < t.vout.length
      · simp [hs, hout, Nat.not_le.mpr hi, hsh ht (fun _ => hi), Spec.transparentSighash?, hb',
          Spec.SignableInput.Restrictions]
      · simp [hs, hout, Nat.le_of_not_lt hi, Spec.transparentSighash?, hb',
          Spec.SignableInput.Restrictions, hi]
    · have hns : (ht.base == .single) = false := by simpa using hs
      simp [hns, hsh ht (fun h => absurd h hs), Spec.transparentSighash?, hb',
        Spec.SignableInput.Restrictions, hs]

/-- **The full signature check, for versions 5 and 6.** `zcash_script`'s `check_sig` with
    Zakura's callback is the public key's validity and the specification's `checkSig`
    (`OP_CHECKSIG`'s check), and never panics. -/
theorem checkSig_v5 (sigHasher : SigHasher) (version : ℕ) (hv : 5 ≤ version)
    (outputsLen : ℕ) (hout : outputsLen = t.vout.length) (i : Fin t.vin.length)
    (scriptCode : List Byte)
    (hsh : ∀ ht : Spec.HashType, (ht.base = .single → i.val < t.vout.length) →
      sigHasher.sighash (zHashType ht) (some (i.val, scriptCode)) =
        some (Spec.signatureDigest H v br hd sp od (.transparent ht i)).toList)
    (b : Byte) (hashType : HashType) (hb : hashType.rawBits = b.setWidth 32)
    (pubkeyValid : Bool) (verify : Blake2bHash → Bool) :
    checkSig pubkeyValid verify
        (calculateSighash sigHasher version outputsLen i.val scriptCode hashType) =
      some (pubkeyValid && Spec.checkSig (fun d => verify d.toList)
        (Spec.transparentSighash? H v br hd sp od i b)) := by
  rw [calculateSighash_v5 H v br hd sp od sigHasher version hv outputsLen hout i scriptCode hsh b
    hashType hb]
  cases pubkeyValid <;> cases Spec.transparentSighash? H v br hd sp od i b <;>
    simp [checkSig, Spec.checkSig]

end

/-- **Versions 3 and 4.** The callback hashes the signature's own hash-type byte, whatever it
    is: every byte gives a digest (ZIP 143 has no undefined hash type), and the byte is the one
    the digest commits to, not a canonical form (GHSA-8m29's V4 case). It panics only where the
    `SigHasher` does (`hsh` assumes it gives a digest). -/
theorem calculateSighash_v4 (sigHasher : SigHasher) (version : ℕ) (hv : version < 5)
    (outputsLen inputIndex : ℕ) (scriptCode : List Byte) (b : Byte) (hashType : HashType)
    (hb : hashType.rawBits = b.setWidth 32) (d : Blake2bHash)
    (hsh : sigHasher.sighashV4Raw b (some (inputIndex, scriptCode)) = some d) :
    calculateSighash sigHasher version outputsLen inputIndex scriptCode hashType =
      some (some d) := by
  have hbyte : (b.setWidth 32 : BitVec 32).setWidth 8 = b := by
    apply BitVec.eq_of_toNat_eq; simp
  have hlt : b.toNat % 4294967296 < 256 := by have := b.isLt; omega
  simp [calculateSighash, hv, hb, hbyte, hsh, hlt]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Script.calculateSighash_v5' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms calculateSighash_v5

/--
info: 'ZcashSighash.Verifier.Script.checkSig_v5' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkSig_v5

/--
info: 'ZcashSighash.Verifier.Script.calculateSighash_v4' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms calculateSighash_v4

end ZcashSighash.Verifier.Script
