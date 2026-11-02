/-
What the digests are written through: `zcash_primitives` 0.31.0's `StateWrite`, a
`blake2b_simd` state behind `corez::io::Write` (`src/encoding.rs`), and `zcash_encoding` 0.5.0's
`CompactSize`, `Vector` and `Array` writers (`src/lib.rs`).

Rust's `u8`, `u32` and `u64` are bit vectors of their width; an `i64` is its 64-bit two's
complement pattern. An `io::Result` is an `Except`, and a panic is `none`.
-/
module

public import ZcashSighash.Spec
public import ZcashSighash.Verifier.Blake2b

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes)

/-- `io::Result<T>`; the error's contents are never read. -/
abbrev IoResult (α : Type) := Except Unit α

/-- `Result::unwrap`, `Result::expect`: the value, or a panic. -/
def unwrap {ε α : Type} : Except ε α → Option α
  | .ok a => some a
  | .error _ => none

/-- `to_le_bytes` of an `n`-byte integer: its bytes, least significant first. -/
def toLeBytes {w : ℕ} (n : ℕ) (x : BitVec w) : List Byte :=
  (List.range n).map fun j => BitVec.ofNat 8 (x.toNat / 256 ^ j)

/-- `blake2b_simd::Hash`, as `as_bytes` gives it. -/
abbrev Blake2bHash := List Byte

/-- BLAKE2b-256 with a personalization, as the specification's hash. -/
def blake2b256 : Spec.Hash := fun p x =>
  ⟨(Blake2b.blake2b 32 (p.toList.map (·.toNat)) (x.map (·.toNat))).map (BitVec.ofNat 8),
    by simp [Blake2b.length_blake2b]⟩

/-- `StateWrite` (`src/encoding.rs`, line 66). -/
structure StateWrite where
  state : Blake2b.State

/-- `Write::write_all` on a `StateWrite`. Its `write` (`src/encoding.rs`, lines 75–78) absorbs the
    whole buffer and returns its length, so `write_all` calls it once and succeeds. -/
def StateWrite.writeAll (self : StateWrite) (buf : List Byte) : IoResult StateWrite :=
  .ok ⟨self.state.update (buf.map (·.toNat))⟩

/-- `corez::io::Write`, through `write_all`, all the digests call. -/
class Write (W : Type) where
  writeAll : W → List Byte → IoResult W

instance : Write StateWrite := ⟨StateWrite.writeAll⟩

/-- `Vec<u8>`: `write_all` extends it. -/
abbrev VecU8 := List Byte

instance : Write VecU8 := ⟨fun v buf => .ok (v ++ buf)⟩

/-- `StateWrite::finalize` (`src/encoding.rs`, lines 69–71), as bytes. -/
def StateWrite.finalize (self : StateWrite) : Blake2bHash :=
  self.state.finalize.map (BitVec.ofNat 8)

/-- `WriteBytesExt::write_u32_le` (`src/encoding.rs`, lines 57–59). -/
def StateWrite.writeU32Le (self : StateWrite) (value : BitVec 32) : IoResult StateWrite :=
  self.writeAll (toLeBytes 4 value)

/-- `hasher` (`src/transaction/txid.rs`, lines 105–107; `src/transaction/sighash_v5.rs`, lines
    29–31, the same):

```rust
StateWrite(Params::new().hash_length(32).personal(personal).to_state())
``` -/
def hasher (personal : Bytes 16) : Option StateWrite := do
  let params ← Blake2b.Params.new.hashLength? 32
  let params ← params.personal? (personal.toList.map (·.toNat))
  pure ⟨params.toState⟩

/-! ## `zcash_encoding` 0.5.0 -/

/-- `MAX_COMPACT_SIZE` (`src/lib.rs`, line 26). -/
def MAX_COMPACT_SIZE : ℕ := 0x02000000

/-- `CompactSize::write_unbounded` (`src/lib.rs`, lines 129–145). -/
def CompactSize.writeUnbounded {W : Type} [Write W] (writer : W) (value : BitVec 64) :
    IoResult W :=
  let n := value.toNat
  if n < 253 then Write.writeAll writer [BitVec.ofNat 8 n]
  else if n ≤ 0xFFFF then do
    let writer ← Write.writeAll writer [253]
    Write.writeAll writer (toLeBytes 2 (BitVec.ofNat 16 n))
  else if n ≤ 0xFFFFFFFF then do
    let writer ← Write.writeAll writer [254]
    Write.writeAll writer (toLeBytes 4 (BitVec.ofNat 32 n))
  else do
    let writer ← Write.writeAll writer [255]
    Write.writeAll writer (toLeBytes 8 value)

/-- `CompactSize::write` (`src/lib.rs`, lines 114–122): an error above `MAX_COMPACT_SIZE`. A
    `usize` fits in a `u64`, so `size as u64` keeps `size`. -/
def CompactSize.write {W : Type} [Write W] (writer : W) (size : ℕ) : IoResult W :=
  if size > MAX_COMPACT_SIZE then .error ()
  else CompactSize.writeUnbounded writer (BitVec.ofNat 64 size)

/-- `Vector::write` (`src/lib.rs`, lines 199–204), through `Vector::write_sized` (lines
    223–233): the length, then each element. -/
def Vector.write {W E : Type} [Write W] (writer : W) (vec : List E)
    (func : W → E → IoResult W) : IoResult W := do
  let writer ← CompactSize.write writer vec.length
  vec.foldlM func writer

/-- `Array::write` (`src/lib.rs`, lines 287–297): each element. -/
def Array.write {W E : Type} (writer : W) (vec : List E) (func : W → E → IoResult W) :
    IoResult W :=
  vec.foldlM func writer

end ZcashSighash.Verifier
