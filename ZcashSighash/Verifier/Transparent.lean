/-
The transparent parts of a transaction and the ZIP 244 sighash types, as `zcash_transparent`
0.11.0 defines them (`src/address.rs`, `src/bundle.rs`, `src/sighash.rs`).

A `Zatoshis` (`zcash_protocol` 0.11.0, `src/value.rs`, line 270) is its `u64`; its
`to_i64_le_bytes` (lines 353–355) casts it to an `i64`, which keeps its 64 bits.
-/
module

public import ZcashSighash.Verifier.Encoding

@[expose] public section

namespace ZcashSighash.Verifier.Transparent

open Spec (Byte Bytes)

/-- `Script` (`src/address.rs`, line 18): its bytes. -/
structure Script where
  code : List Byte

/-- `Script::write` (`src/address.rs`, lines 68–70). -/
def Script.write (self : Script) (writer : StateWrite) : IoResult StateWrite :=
  Vector.write writer self.code fun w e => w.writeAll [e]

/-- `OutPoint` (`src/bundle.rs`, lines 152–157). -/
structure OutPoint where
  hash : Bytes 32
  n : BitVec 32

/-- `OutPoint::write` (`src/bundle.rs`, lines 198–201). -/
def OutPoint.write (self : OutPoint) (writer : StateWrite) : IoResult StateWrite := do
  let writer ← writer.writeAll self.hash.toList
  writer.writeAll (toLeBytes 4 self.n)

/-- `OutPoint::is_null` (`src/bundle.rs`, lines 205–207): equal to `OutPoint::NULL` (lines
    163–166), the zero txid and `u32::MAX`. -/
def OutPoint.isNull (self : OutPoint) : Bool :=
  self.hash.toList == List.replicate 32 0 && self.n == 0xffffffff

/-- `TxIn` (`src/bundle.rs`, lines 226–233). Its `script_sig` is that of
    `transparent::Authorized`, a `Script`. -/
structure TxIn where
  prevout : OutPoint
  scriptSig : Script
  sequence : BitVec 32

/-- `TxOut` (`src/bundle.rs`, lines 368–373), its value a `Zatoshis`. -/
structure TxOut where
  value : BitVec 64
  scriptPubkey : Script

/-- `TxOut::write` (`src/bundle.rs`, lines 400–403). -/
def TxOut.write (self : TxOut) (writer : StateWrite) : IoResult StateWrite := do
  let writer ← writer.writeAll (toLeBytes 8 self.value)
  self.scriptPubkey.write writer

/-- What `TransparentAuthorizingContext` (`src/sighash.rs`, lines 126–137) gives: the amounts and
    `scriptPubKey`s of the coins the inputs spend. -/
structure AuthorizingContext where
  inputAmounts : List (BitVec 64)
  inputScriptpubkeys : List Script

/-- `Bundle` (`src/bundle.rs`, lines 81–85). The Lean holds both kinds of authorization the
    digests read: each input's `script_sig` (`Authorized`), for the auth digest, and the
    authorizing context, for the signature digests. -/
structure Bundle where
  vin : List TxIn
  vout : List TxOut
  authorization : AuthorizingContext

/-- `Bundle::is_coinbase` (`src/bundle.rs`, lines 94–98). -/
def Bundle.isCoinbase (self : Bundle) : Bool :=
  match self.vin with
  | [input] => input.prevout.isNull
  | _ => false

/-! ## Sighash types (`src/sighash.rs`) -/

/-- `SIGHASH_ALL` (line 11). -/
def SIGHASH_ALL : Byte := 0x01
/-- `SIGHASH_NONE` (line 12). -/
def SIGHASH_NONE : Byte := 0x02
/-- `SIGHASH_SINGLE` (line 13). -/
def SIGHASH_SINGLE : Byte := 0x03
/-- `SIGHASH_MASK` (line 14). -/
def SIGHASH_MASK : Byte := 0x1f
/-- `SIGHASH_ANYONECANPAY` (line 15). -/
def SIGHASH_ANYONECANPAY : Byte := 0x80

/-- `SighashType` (line 21). -/
structure SighashType where
  byte : Byte

/-- `SighashType::parse` (lines 34–39). -/
def SighashType.parse (hashType : Byte) : Option SighashType :=
  let b := hashType &&& ~~~SIGHASH_ANYONECANPAY
  if b = SIGHASH_ALL ∨ b = SIGHASH_NONE ∨ b = SIGHASH_SINGLE then some ⟨hashType⟩ else none

/-- `SighashType::encode` (lines 50–53). -/
def SighashType.encode (self : SighashType) : Byte := self.byte

/-- `SignableInput` (lines 160–166). Its `script_code` is never read by the version 5 and 6
    digests. -/
structure SignableInput where
  hashType : SighashType
  index : ℕ
  scriptPubkey : Script
  value : BitVec 64

/-- `SignableInput::from_parts` (lines 170–192): an error for an index out of range. -/
def SignableInput.fromParts (bundle : Bundle) (hashType : SighashType) (index : ℕ)
    (scriptPubkey : Script) (value : BitVec 64) : Except Unit SignableInput :=
  if index ≥ bundle.vin.length then .error ()
  else .ok ⟨hashType, index, scriptPubkey, value⟩

end ZcashSighash.Verifier.Transparent
