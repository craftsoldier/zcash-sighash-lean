/-
`zcash_script` 0.6.0's `push_num` (`src/pattern.rs`), which Zakura encodes a coinbase input's
height with, and what it calls: `num::serialize` (`src/num.rs`), `PushValue::from_slice`
(`src/opcode/mod.rs`, `src/opcode/push_value.rs`), with `bounded-vec` 0.9.0's
`BoundedVec::try_from` (`src/bounded_vec.rs`), and the `to_bytes` of the `PushValue` it gives.
-/
module

public import ZcashSighash.Verifier.Encoding

@[expose] public section

namespace ZcashSighash.Verifier.PushNum

open Spec (Byte)

/-- The loop of `serialize` (`src/num.rs`, lines 101–108): `absvalue`'s bytes, least
    significant first. `absvalue` is not negative (`serialize` returns early for `i64::MIN`), so
    its `>>=` is a logical shift, and the `try_into` of a byte cannot panic. -/
def serializeLoop (absvalue : BitVec 64) : List Byte :=
  if absvalue = 0 then []
  else (absvalue &&& 0xff).setWidth 8 :: serializeLoop (absvalue >>> 8)
termination_by absvalue.toNat
decreasing_by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have : absvalue.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using ‹¬absvalue = 0›
  exact Nat.div_lt_self (by omega) (by decide)

/-- `serialize` (`src/num.rs`, lines 85–125). -/
def serialize (value : BitVec 64) : List Byte :=
  if value = 0 then []
  else if value = BitVec.intMin 64 then [0, 0, 0, 0, 0, 0, 0, 128, 128]
  else
    let neg := value.slt 0
    let result := serializeLoop value.abs
    if result.getLast?.all (fun last => last &&& 0x80 ≠ 0) then
      result ++ [if neg then 0x80 else 0]
    else if neg then result.dropLast ++ result.getLast?.toList.map (· ||| 0x80)
    else result

/-- `SmallValue` (`src/opcode/push_value.rs`, lines 249–273). -/
inductive SmallValue where
  | OP_0 | OP_1NEGATE | OP_1 | OP_2 | OP_3 | OP_4 | OP_5 | OP_6 | OP_7 | OP_8 | OP_9 | OP_10
  | OP_11 | OP_12 | OP_13 | OP_14 | OP_15 | OP_16
  deriving DecidableEq

/-- `SmallValue::encode` (lines 303–307): the discriminant (lines 253–272). -/
def SmallValue.encode : SmallValue → Byte
  | .OP_0 => 0x00 | .OP_1NEGATE => 0x4f | .OP_1 => 0x51 | .OP_2 => 0x52 | .OP_3 => 0x53
  | .OP_4 => 0x54 | .OP_5 => 0x55 | .OP_6 => 0x56 | .OP_7 => 0x57 | .OP_8 => 0x58
  | .OP_9 => 0x59 | .OP_10 => 0x5a | .OP_11 => 0x5b | .OP_12 => 0x5c | .OP_13 => 0x5d
  | .OP_14 => 0x5e | .OP_15 => 0x5f | .OP_16 => 0x60

/-- `LargeValue` (lines 18–29), each `BoundedVec` as its contents. -/
inductive LargeValue where
  | PushdataBytelength (bv : List Byte)
  | OP_PUSHDATA1 (bv : List Byte)
  | OP_PUSHDATA2 (bv : List Byte)
  | OP_PUSHDATA4 (bv : List Byte)

/-- `LargeValue::MAX_SIZE` (line 39). -/
def LargeValue.MAX_SIZE : ℕ := 520

/-- `BoundedVec::<T, L, U>::try_from` (`bounded-vec` 0.9.0, `src/bounded_vec.rs`, lines 478–494,
    through `from_vec`, lines 90–104 for `L = 0` and 240–259 otherwise): the vector, if its
    length is in `L..=U`. -/
def boundedVecTryFrom (L U : ℕ) (v : List Byte) : Option (List Byte) :=
  if v.length < L then none
  else if v.length > U then none
  else some v

/-- `LargeValue::from_slice` (`src/opcode/push_value.rs`, lines 53–65). -/
def LargeValue.fromSlice (v : List Byte) : Option LargeValue :=
  if let some bv := boundedVecTryFrom 1 0x4b v then some (.PushdataBytelength bv)
  else if let some bv := boundedVecTryFrom 0 0xff v then some (.OP_PUSHDATA1 bv)
  else if let some bv := boundedVecTryFrom 0 MAX_SIZE v then some (.OP_PUSHDATA2 bv)
  else if let some bv := boundedVecTryFrom 0 MAX_SIZE v then some (.OP_PUSHDATA4 bv)
  else none

/-- `From<&LargeValue> for Vec<u8>` (lines 196–215). The length's `expect` cannot panic: a
    `BoundedVec` holds at most `MAX_SIZE` bytes. -/
def LargeValue.toBytes (value : LargeValue) : List Byte :=
  let toVec (pref : Option Byte) (contents : List Byte) : List Byte :=
    pref.toList ++ serialize (BitVec.ofNat 64 contents.length) ++ contents
  match value with
  | .PushdataBytelength bv => toVec none bv
  | .OP_PUSHDATA1 bv => toVec (some 0x4c) bv
  | .OP_PUSHDATA2 bv => toVec (some 0x4d) bv
  | .OP_PUSHDATA4 bv => toVec (some 0x4e) bv

/-- `PushValue` (`src/opcode/mod.rs`, lines 87–93). -/
inductive PushValue where
  | SmallValue (v : SmallValue)
  | LargeValue (v : LargeValue)

/-- `PushValue::from_slice` (lines 97–119). -/
def PushValue.fromSlice (v : List Byte) : Option PushValue :=
  match v.map (·.toNat) with
  | [] => some (.SmallValue .OP_0)
  | [0x81] => some (.SmallValue .OP_1NEGATE)
  | [1] => some (.SmallValue .OP_1)
  | [2] => some (.SmallValue .OP_2)
  | [3] => some (.SmallValue .OP_3)
  | [4] => some (.SmallValue .OP_4)
  | [5] => some (.SmallValue .OP_5)
  | [6] => some (.SmallValue .OP_6)
  | [7] => some (.SmallValue .OP_7)
  | [8] => some (.SmallValue .OP_8)
  | [9] => some (.SmallValue .OP_9)
  | [10] => some (.SmallValue .OP_10)
  | [11] => some (.SmallValue .OP_11)
  | [12] => some (.SmallValue .OP_12)
  | [13] => some (.SmallValue .OP_13)
  | [14] => some (.SmallValue .OP_14)
  | [15] => some (.SmallValue .OP_15)
  | [16] => some (.SmallValue .OP_16)
  | _ => (LargeValue.fromSlice v).map .LargeValue

/-- `PushValue::to_bytes` (lines 183–185), through `From<&PushValue> for Vec<u8>`
    (lines 1064–1071). -/
def PushValue.toBytes : PushValue → List Byte
  | .SmallValue v => [v.encode]
  | .LargeValue v => v.toBytes

/-- `push_value` (`src/pv.rs`, lines 29–33). -/
def pushValue (value : List Byte) : Option PushValue := PushValue.fromSlice value

/-- `serialize`'s loop gives one byte per byte of its argument. -/
theorem serializeLoop_length {k : ℕ} {x : BitVec 64} (hx : x.toNat < 256 ^ k) :
    (serializeLoop x).length ≤ k := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := by apply BitVec.eq_of_toNat_eq; simp at hx; simp [hx]
    simp [serializeLoop, this]
  | succ k ih =>
    unfold serializeLoop
    split
    · simp
    · simp only [List.length_cons, Nat.add_le_add_iff_right]
      apply ih
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [Nat.pow_succ] at hx
      exact Nat.div_lt_of_lt_mul (by omega)

/-- `serialize` gives at most 9 bytes. -/
theorem serialize_length (n : BitVec 64) : (serialize n).length ≤ 9 := by
  have h8 := serializeLoop_length (k := 8) (x := n.abs) (by have := n.abs.isLt; omega)
  unfold serialize
  split
  · simp
  split
  · simp
  dsimp only
  split
  · simp only [List.length_append, List.length_singleton]; omega
  split
  · simp only [List.length_append, List.length_dropLast, List.length_map]
    cases h : (serializeLoop n.abs).getLast? <;> simp <;> omega
  · omega

/-- `LargeValue::from_slice` accepts every value of at most `MAX_SIZE` bytes. -/
theorem largeValue_fromSlice_isSome {v : List Byte} (hv : v.length ≤ LargeValue.MAX_SIZE) :
    (LargeValue.fromSlice v).isSome := by
  unfold LargeValue.fromSlice boundedVecTryFrom LargeValue.MAX_SIZE at *
  by_cases h1 : v.length < 1 <;> by_cases h2 : v.length > 0x4b <;>
    by_cases h3 : v.length > 0xff <;> simp [h1, h2, h3, show ¬v.length > 520 by omega]

/-- `push_value` accepts every value of at most `MAX_SIZE` bytes. -/
theorem pushValue_isSome {v : List Byte} (hv : v.length ≤ LargeValue.MAX_SIZE) :
    (pushValue v).isSome := by
  unfold pushValue PushValue.fromSlice
  split
  all_goals first | rfl | simpa using largeValue_fromSlice_isSome hv

/-- `push_num`'s `expect` never panics: `push_value` accepts what `serialize` gives. -/
theorem pushValue_serialize_isSome (n : BitVec 64) : (pushValue (serialize n)).isSome :=
  pushValue_isSome (by have := serialize_length n; unfold LargeValue.MAX_SIZE; omega)

/-- `push_num` (`src/pattern.rs`, lines 196–199). The `expect` cannot panic
    (`pushValue_serialize_isSome`). -/
def pushNum (n : BitVec 64) : PushValue :=
  (pushValue (serialize n)).get (pushValue_serialize_isSome n)

end ZcashSighash.Verifier.PushNum
