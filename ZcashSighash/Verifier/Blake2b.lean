/-
BLAKE2b (RFC 7693), and the parts of the `blake2b_simd 1.0.4` interface `zcash_primitives` calls.

`blake2b` computes the hash. It is the plain sequential algorithm of RFC 7693, §3. Copied from
craftsoldier/equihash-lean (`Equihash/Verifier/Blake2b.lean`), without its Equihash `HashFn`, and
with its loops over `List.range`, which the kernel can evaluate from a module (`[0:n]` loops it
cannot), so that a proof can compute a digest.
-/
module

public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace ZcashSighash.Verifier.Blake2b

/-! ## BLAKE2b (RFC 7693) -/

/-- The initialization vector (RFC 7693, §2.6). -/
def iv : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message schedule (RFC 7693, §2.7). -/
def sigma : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotation right by `n` bits. -/
def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function `G` (RFC 7693, §3.1). -/
def mix (v : Array UInt64) (a b c d : ℕ) (x y : UInt64) : Array UInt64 :=
  let v := v.set! a (v[a]! + v[b]! + x)
  let v := v.set! d (rotr (v[d]! ^^^ v[a]!) 32)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotr (v[b]! ^^^ v[c]!) 24)
  let v := v.set! a (v[a]! + v[b]! + y)
  let v := v.set! d (rotr (v[d]! ^^^ v[a]!) 16)
  let v := v.set! c (v[c]! + v[d]!)
  v.set! b (rotr (v[b]! ^^^ v[c]!) 63)

/-- Word `i` of a sequence of bytes: bytes `8i .. 8i + 8`, little-endian, zero past the end. -/
def word (bytes : List ℕ) (i : ℕ) : UInt64 :=
  (List.range 8).foldr (fun j w => (w <<< 8) ||| UInt64.ofNat (bytes.getD (8 * i + j) 0)) 0

/-- The compression function `F` (RFC 7693, §3.2): `t` bytes processed so far, `last` for
    the final block. -/
def compress (h : Array UInt64) (block : List ℕ) (t : ℕ) (last : Bool) : Array UInt64 := Id.run do
  let m := (List.range 16).toArray.map (word block)
  let mut v := h ++ iv
  v := v.set! 12 (v[12]! ^^^ UInt64.ofNat t)
  v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (t / 2 ^ 64))
  if last then
    v := v.set! 14 (~~~v[14]!)
  for i in List.range 12 do
    let s := sigma[i % 10]!
    v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  return (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- The final state of `BLAKE2b` with an `outLen`-byte output, a 16-byte personalization, no
    key and no salt, after hashing `input` (RFC 7693, §3.3). RFC 7693's parameter block (§2.5)
    has no personalization; the block here is `blake2b_simd 1.0.4`'s (`Params::to_words`,
    `src/lib.rs`, lines 185–204), with the personalization in words 6 and 7. -/
def finalState (outLen : ℕ) (personal input : List ℕ) : Array UInt64 := Id.run do
  -- Parameter block: digest length, key length 0, fanout 1, depth 1; personalization.
  let mut h := iv
  h := h.set! 0 (h[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat outLen)
  h := h.set! 6 (h[6]! ^^^ word personal 0)
  h := h.set! 7 (h[7]! ^^^ word personal 1)
  -- The input in 128-byte blocks; an empty input is one empty block.
  let blocks := max 1 ((input.length + 127) / 128)
  for i in List.range blocks do
    let last := i + 1 == blocks
    let t := if last then input.length else 128 * (i + 1)
    h := compress h ((input.drop (128 * i)).take 128) t last
  return h

/-- `BLAKE2b`: the first `outLen` bytes of the final state, little-endian. -/
def blake2b (outLen : ℕ) (personal input : List ℕ) : List ℕ :=
  let h := finalState outLen personal input
  List.ofFn fun (i : Fin outLen) => (h[i.val / 8]! >>> UInt64.ofNat (8 * (i.val % 8))).toNat % 256

theorem length_blake2b (outLen : ℕ) (personal input : List ℕ) :
    (blake2b outLen personal input).length = outLen := by
  simp [blake2b]

/-! ## The `blake2b_simd` interface -/

/-- `OUTBYTES`: the largest output length, in bytes. -/
def outBytes : ℕ := 64

/-- `PERSONALBYTES`: the length of a personalization, in bytes. -/
def personalBytes : ℕ := 16

/-- `blake2b_simd::Params`, reduced to the fields `zcash_primitives` sets. -/
structure Params where
  hashLength : ℕ
  personal : List ℕ

/-- `Params::new`: output length `OUTBYTES`, zero personalization. -/
def Params.new : Params := { hashLength := outBytes, personal := List.replicate personalBytes 0 }

/-- `Params::hash_length`:

```rust
assert!(1 <= length && length <= OUTBYTES, "Bad hash length: {}", length);
self.hash_length = length as u8;
``` -/
def Params.hashLength? (self : Params) (length : ℕ) : Option Params := do
  guard (1 ≤ length ∧ length ≤ outBytes)
  return { self with hashLength := length }

/-- `Params::personal`:

```rust
assert!(personalization.len() <= PERSONALBYTES, ...);
self.personal = [0; PERSONALBYTES];
self.personal[..personalization.len()].copy_from_slice(personalization);
``` -/
def Params.personal? (self : Params) (personalization : List ℕ) : Option Params := do
  guard (personalization.length ≤ personalBytes)
  return { self with
    personal := personalization ++ List.replicate (personalBytes - personalization.length) 0 }

/-- `blake2b_simd::State`: the parameters it was built from, and the input absorbed so far. -/
structure State where
  params : Params
  input : List ℕ

/-- `Params::to_state`. -/
def Params.toState (self : Params) : State := { params := self, input := [] }

/-- `State::update`. -/
def State.update (self : State) (input : List ℕ) : State :=
  { self with input := self.input ++ input }

/-- `State::finalize`, then `Hash::as_bytes`: the hash of everything absorbed. -/
def State.finalize (self : State) : List ℕ :=
  blake2b self.params.hashLength self.params.personal self.input

end ZcashSighash.Verifier.Blake2b
