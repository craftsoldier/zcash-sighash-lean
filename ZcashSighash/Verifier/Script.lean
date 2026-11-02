/-
The glue between the script interpreter and the signature digests: `zcash_script` 0.6.0's hash
types and signature check (`src/signature.rs`, `src/interpreter.rs`), and `zakura-script`
5.0.0's sighash callback (`src/lib.rs`), which hands each `OP_CHECKSIG` its digest.

The callback calls Zakura's `SigHasher` (`zakura-chain` 10.0.0, `src/transaction/sighash.rs`),
held here as its two methods, `sighash` and `sighash_v4_raw`; either may panic (`none`).
-/
module

public import ZcashSighash.Verifier.Encoding

@[expose] public section

namespace ZcashSighash.Verifier.Script

open Spec (Byte)

/-! ## `zcash_script` 0.6.0 -/

/-- `SignedOutputs` (`src/signature.rs`, lines 112–127). -/
inductive SignedOutputs where
  | all
  | single
  | none
  deriving DecidableEq

/-- `HashType` (lines 130–135); an `i32` is its 32-bit two's complement pattern. -/
structure HashType where
  signedOutputs : SignedOutputs
  anyoneCanPay : Bool
  rawBits : BitVec 32

/-- `InvalidHashType` (lines 19–27). -/
inductive InvalidHashType where
  | invalidSignedOutputs
  | extraBitsSet (bits : BitVec 32)

/-- `HashType::from_bits` (lines 151–168). `Signature::from_bytes` (line 376) passes the
    signature's last byte, widened from `u8`, with `is_strict` false under the consensus flags
    (`P2SH | CHECKLOCKTIMEVERIFY`, no `STRICTENC`). -/
def HashType.fromBits (bits : BitVec 32) (isStrict : Bool) : Except InvalidHashType HashType :=
  let unknownBits := (bits ||| 0x83) ^^^ 0x83
  if isStrict && unknownBits != 0 then .error (.extraBitsSet unknownBits)
  else if isStrict && bits &&& 0x03 == 0 then .error .invalidSignedOutputs
  else .ok
    { signedOutputs := if bits &&& 0x1f == 2 then .none
        else if bits &&& 0x1f == 3 then .single else .all
      anyoneCanPay := bits &&& 0x80 != 0
      rawBits := bits }

/-- `CallbackTransactionSignatureChecker::check_sig` (`src/interpreter.rs`, lines 459–471):
    `pubkey.is_valid() && (self.sighash)(script_code, sig.sighash_type())
    .map(|sighash| pubkey.verify(&sighash, sig.sig())).unwrap_or(false)`, with the public key's
    validity and the signature's verification as parameters. A panic in the callback is `none`. -/
def checkSig (pubkeyValid : Bool) (verify : Blake2bHash → Bool)
    (sighash : Option (Option Blake2bHash)) : Option Bool :=
  if pubkeyValid then (·.any verify) <$> sighash else pure false

/-! ## `zakura-chain` 10.0.0's `HashType` and `SigHasher` -/

/-- `zakura_chain::transaction::HashType` (`src/transaction/sighash.rs`, lines 18–38): a set of
    bit flags in a `u32`. -/
abbrev ZHashType := BitVec 32

/-- `HashType::ALL` (line 23). -/
def ALL : ZHashType := 0x01
/-- `HashType::NONE` (line 25). -/
def NONE : ZHashType := 0x02
/-- `HashType::SINGLE` (line 27). -/
def SINGLE : ZHashType := 0x03
/-- `HashType::ALL_ANYONECANPAY` (line 32). -/
def ALL_ANYONECANPAY : ZHashType := 0x81
/-- `HashType::NONE_ANYONECANPAY` (line 34). -/
def NONE_ANYONECANPAY : ZHashType := 0x82
/-- `HashType::SINGLE_ANYONECANPAY` (line 36). -/
def SINGLE_ANYONECANPAY : ZHashType := 0x83

/-- Zakura's `SigHasher` (`src/transaction/sighash.rs`, lines 157–311), as the two methods the
    callback calls, each given an input index and its script code. A panic is `none`. -/
structure SigHasher where
  /-- `SigHasher::sighash`, for a version 5 or later transaction. -/
  sighash : ZHashType → Option (ℕ × List Byte) → Option Blake2bHash
  /-- `SigHasher::sighash_v4_raw`, for an earlier one, with the signature's hash-type byte. -/
  sighashV4Raw : Byte → Option (ℕ × List Byte) → Option Blake2bHash

/-! ## `zakura-script` 5.0.0, `src/lib.rs` -/

/-- `parse_zip244_hash_type` (lines 76–86). -/
def parseZip244HashType (rawHashType : BitVec 32) : Option ZHashType :=
  match rawHashType with
  | 0x01 => some ALL
  | 0x02 => some NONE
  | 0x03 => some SINGLE
  | 0x81 => some ALL_ANYONECANPAY
  | 0x82 => some NONE_ANYONECANPAY
  | 0x83 => some SINGLE_ANYONECANPAY
  | _ => none

/-- The `calculate_sighash` closure of `CachedFfiTransaction::is_valid` (lines 188–223), for the
    input at `inputIndex` of a transaction of version `version` with `outputsLen` transparent
    outputs. `none` (the outer one) is a panic; `some none` fails this signature check only. -/
def calculateSighash (sigHasher : SigHasher) (version outputsLen inputIndex : ℕ)
    (scriptCode : List Byte) (hashType : HashType) : Option (Option Blake2bHash) := do
  if version < 5 then
    -- `hash_type.raw_bits().try_into().expect(...)`: a panic unless the `i32` is in `0..=255`.
    if 256 ≤ hashType.rawBits.toNat then none
    let rawByte : Byte := hashType.rawBits.setWidth 8
    return some (← sigHasher.sighashV4Raw rawByte (some (inputIndex, scriptCode)))
  match parseZip244HashType hashType.rawBits with
  | none => return none
  | some ourHashType =>
    if (ourHashType == SINGLE || ourHashType == SINGLE_ANYONECANPAY) &&
        inputIndex ≥ outputsLen then
      return none
    return some (← sigHasher.sighash ourHashType (some (inputIndex, scriptCode)))

end ZcashSighash.Verifier.Script
