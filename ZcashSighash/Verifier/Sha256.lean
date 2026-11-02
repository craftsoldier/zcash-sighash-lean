/-
SHA-256 (FIPS 180-4), and the SHA-256d that `zcash_transparent` 0.11.0's `HashReader` and
`HashWriter` (`src/util/sha256d.rs`) compute with the `sha2` crate: SHA-256 of the SHA-256 of
what was read or written.

`sha256` is the plain sequential algorithm of FIPS 180-4, §6.2, over bytes, with its loops over
`List.range`, as `Verifier/Blake2b.lean`'s.
-/
module

public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace ZcashSighash.Verifier.Sha256

/-! ## SHA-256 (FIPS 180-4) -/

/-- The round constants (§4.2.2). -/
def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value (§5.3.3). -/
def h0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- `ROTR^n` (§3.2). -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- `Ch` (§4.1.2). -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj` (§4.1.2). -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀` (§4.1.2). -/
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- `Σ₁` (§4.1.2). -/
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- `σ₀` (§4.1.2). -/
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- `σ₁` (§4.1.2). -/
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The padded message (§5.1.1): the message, a 1 bit, zeros, and its length in bits as a
    64-bit big-endian integer, to a multiple of 64 bytes. -/
def pad (m : List ℕ) : List ℕ :=
  let zeros := (119 - m.length % 64) % 64
  m ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range 8).reverse.map fun j => (8 * m.length) / 256 ^ j % 256

/-- Word `i` of a block: bytes `4i .. 4i + 4`, big-endian (§5.2.1). -/
def word (block : List ℕ) (i : ℕ) : UInt32 :=
  (List.range 4).foldl (fun w j => (w <<< 8) ||| UInt32.ofNat (block.getD (4 * i + j) 0)) 0

/-- The message schedule `W₀ … W₆₃` of a block (§6.2.2, step 1). -/
def schedule (block : List ℕ) : Array UInt32 :=
  (List.range 48).foldl (fun w t =>
      w.push (smallSigma1 w[t + 14]! + w[t + 9]! + smallSigma0 w[t + 1]! + w[t]!))
    ((List.range 16).toArray.map (word block))

/-- The hash computation for one block (§6.2.2, steps 2–4). -/
def compress (h : Array UInt32) (block : List ℕ) : Array UInt32 :=
  let w := schedule block
  let v := (List.range 64).foldl (fun v t =>
      let t1 := v[7]! + bigSigma1 v[4]! + ch v[4]! v[5]! v[6]! + k[t]! + w[t]!
      let t2 := bigSigma0 v[0]! + maj v[0]! v[1]! v[2]!
      #[t1 + t2, v[0]!, v[1]!, v[2]!, v[3]! + t1, v[4]!, v[5]!, v[6]!]) h
  (List.range 8).toArray.map fun i => h[i]! + v[i]!

/-- SHA-256 of a message: its digest, as 32 bytes. -/
def sha256 (m : List ℕ) : List ℕ :=
  let p := pad m
  let h := (List.range (p.length / 64)).foldl (fun h i =>
    compress h ((p.drop (64 * i)).take 64)) h0
  (List.range 32).map fun i => ((h[i / 4]! >>> (8 * (3 - (i % 4)).toUInt32)).toNat % 256)

/-- SHA-256d: SHA-256 of the SHA-256 of a message, as `HashReader::into_hash` and
    `HashWriter::into_hash` (lines 25–27 and 57–59) compute it. -/
def sha256d (m : List ℕ) : List ℕ := sha256 (sha256 m)

end ZcashSighash.Verifier.Sha256
