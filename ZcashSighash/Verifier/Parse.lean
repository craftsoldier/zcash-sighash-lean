/-
Zakura's parser for transparent inputs and outputs: `zakura-chain` 10.0.0,
`src/transparent/serialize.rs`, and the readers it calls (`src/serialization/`). A parse error is
`none`.

The reader's allocation bounds (`ZcashReader`'s `remaining` and `limit`, `MAX_U8_ALLOCATION`,
`T::max_allocation`) only reject more inputs, so they are left out: what this parser returns on
success is what Zakura's returns, and `Proofs/Parse.lean` is about what a successful parse
returns.
-/
module

public import ZcashSighash.Verifier.Native
public import ZcashSighash.Verifier.PushNum

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes)

/-- A parser over the bytes left to read; `none` is an error. -/
abbrev Parser := StateT (List Byte) Option

/-- A `SerializationError`. -/
def fail {α : Type} : Parser α := fun _ => none

/-- `Read::read_exact` of `n` bytes: an error at the end of the input. -/
def readBytes (n : ℕ) : Parser (List Byte) := fun s =>
  if n ≤ s.length then some (s.take n, s.drop n) else none

/-- `read_u8`, and `read_u16`, `read_u32` and `read_u64` `::<LittleEndian>`: `n` bytes,
    little-endian. -/
def readLe (n : ℕ) : Parser ℕ := do
  let bytes ← readBytes n
  pure (bytes.foldr (fun b acc => b.toNat + 256 * acc) 0)

/-- `read_32_bytes` (`src/serialization/read_zcash.rs`, lines 25–29). -/
def read32Bytes : Parser (Bytes 32) := do
  let bytes ← readBytes 32
  if h : bytes.length = 32 then pure ⟨bytes, h⟩ else fail

/-- `CompactSize64::zcash_deserialize` (`src/serialization/compact_size.rs`, lines 365–388): an
    error for a non-canonical encoding. -/
def readCompactSize64 : Parser ℕ := do
  let flag ← readLe 1
  if flag ≤ 0xfc then pure flag
  else if flag = 0xfd then do
    let n ← readLe 2
    if 0xfd ≤ n then pure n else fail
  else if flag = 0xfe then do
    let n ← readLe 4
    if 0x10000 ≤ n then pure n else fail
  else do
    let n ← readLe 8
    if 0x100000000 ≤ n then pure n else fail

/-- `CompactSizeMessage::zcash_deserialize` (lines 309–319), through
    `CompactSizeMessage::try_from(usize)` (lines 233–256): an error for a size that does not fit
    a `u32` or exceeds `MAX_PROTOCOL_MESSAGE_LEN`. -/
def readCompactSizeMessage : Parser ℕ := do
  let size ← readCompactSize64
  if 2 ^ 32 ≤ size then fail
  if size > MAX_PROTOCOL_MESSAGE_LEN then fail
  pure size

/-- `Vec<u8>::zcash_deserialize` (`src/serialization/zcash_deserialize.rs`, lines 111–118), and
    so `Script::zcash_deserialize` (`src/transparent/script.rs`, lines 108–114). -/
def readByteVec : Parser (List Byte) := do
  let len ← readCompactSizeMessage
  readBytes len

/-- `read_external_count`'s loop (`src/serialization/zcash_deserialize.rs`, lines 182–190). -/
def readCount {α : Type} (read : Parser α) : ℕ → Parser (List α)
  | 0 => pure []
  | n + 1 => do
    let a ← read
    let as ← readCount read n
    pure (a :: as)

/-- `Vec<T>::zcash_deserialize` (lines 84–91). -/
def readVec {α : Type} (read : Parser α) : Parser (List α) := do
  let len ← readCompactSizeMessage
  readCount read len

/-- `MIN_COINBASE_SCRIPT_LEN` (`zakura-transparent` 4.0.0, `src/coinbase.rs`, line 10). -/
def MIN_COINBASE_SCRIPT_LEN : ℕ := 2

/-- `MAX_COINBASE_SCRIPT_LEN` (`zakura-transparent` 4.0.0, `src/coinbase.rs`, line 17). -/
def MAX_COINBASE_SCRIPT_LEN : ℕ := 100

/-- `GENESIS_COINBASE_SCRIPT_SIG` (`src/transparent/serialize.rs`, lines 24–29). -/
def GENESIS_COINBASE_SCRIPT_SIG : List Byte :=
  [4, 255, 255, 7, 31, 1, 4, 69, 90, 99, 97, 115, 104, 48, 98, 57, 99, 52, 101, 101, 102, 56, 98,
    55, 99, 99, 52, 49, 55, 101, 101, 53, 48, 48, 49, 101, 51, 53, 48, 48, 57, 56, 52, 98, 54,
    102, 101, 97, 51, 53, 54, 56, 51, 97, 55, 99, 97, 99, 49, 52, 49, 97, 48, 52, 51, 99, 52, 50,
    48, 54, 52, 56, 51, 53, 100, 51, 52]

/-- The `CoinbaseScript` of Zakura's `coinbase_script` (`src/transparent.rs`, lines 173–188):
    `push_num(height.into()).to_bytes()`, `From<Height> for i64` zero-extending the `u32`
    (`src/block/height.rs`, lines 185–189), and the genesis `scriptSig`. -/
def CoinbaseScript.zakura : CoinbaseScript :=
  ⟨fun height => (PushNum.pushNum (height.setWidth 64)).toBytes, GENESIS_COINBASE_SCRIPT_SIG⟩

/-- `Height::MAX` (`src/block/height.rs`, line 81): `u32::MAX / 2`. -/
def HEIGHT_MAX : ℕ := (2 ^ 32 - 1) / 2

/-- `parse_coinbase_height`'s candidate height and prefix length (lines 63–79): a small number
    opcode, or a push of one to five bytes, zero-extended, so never negative. -/
def candidateHeight (scriptSig : List Byte) : Option (ℕ × ℕ) := do
  let first ← scriptSig.head?
  if 0x51 ≤ first.toNat ∧ first.toNat ≤ 0x60 then some (first.toNat - 0x50, 1)
  else if 1 ≤ first.toNat ∧ first.toNat ≤ 5 then
    let n := first.toNat
    if scriptSig.length < n + 1 then none
    else some (((scriptSig.drop 1).take n).foldr (fun b acc => b.toNat + 256 * acc) 0, 1 + n)
  else none

/-- `parse_coinbase_height` (`src/transparent/serialize.rs`, lines 58–96). The candidate height
    is below `2 ^ 40`, so it is its `i64`. -/
def parseCoinbaseHeight (scriptSig : List Byte) : Option (BitVec 32 × List Byte) := do
  let (h, len) ← candidateHeight scriptSig
  if scriptSig.length < len then none
  if scriptSig.take len ≠ (PushNum.pushNum (BitVec.ofNat 64 h)).toBytes then none
  if 2 ^ 32 ≤ h then none
  if h > HEIGHT_MAX then none
  pure (BitVec.ofNat 32 h, scriptSig.drop len)

/-- `Input::zcash_deserialize` (lines 169–227). -/
def readInput : Parser Input := do
  let hash ← read32Bytes
  if hash.toList = List.replicate 32 0 then
    if (← readLe 4) ≠ 0xffffffff then fail
    let len ← readCompactSizeMessage
    if len < MIN_COINBASE_SCRIPT_LEN then fail
    if len > MAX_COINBASE_SCRIPT_LEN then fail
    let scriptSig ← readBytes len
    let (height, data) ← if scriptSig = GENESIS_COINBASE_SCRIPT_SIG
      then pure (0, GENESIS_COINBASE_SCRIPT_SIG)
      else liftM (parseCoinbaseHeight scriptSig)
    let sequence ← readLe 4
    pure (.coinbase height data (BitVec.ofNat 32 sequence))
  else
    let index ← readLe 4
    let unlockScript ← readByteVec
    let sequence ← readLe 4
    pure (.prevOut ⟨hash, BitVec.ofNat 32 index⟩ unlockScript (BitVec.ofNat 32 sequence))

/-- `MAX_MONEY` (`src/amount.rs`, lines 655–658): 21 million coins of 10^8 zatoshis. -/
def MAX_MONEY : ℕ := 21000000 * 100000000

/-- `Output::zcash_deserialize` (lines 237–248), with `Amount<NonNegative>`'s
    (`src/amount.rs`, lines 709–715, through `TryFrom<u64>`, lines 310–324, and
    `NonNegative`'s range, lines 628–632). -/
def readOutput : Parser Output := do
  let value ← readLe 8
  if value > MAX_MONEY then fail
  let lockScript ← readByteVec
  pure ⟨BitVec.ofNat 64 value, lockScript⟩

end ZcashSighash.Verifier.Native
