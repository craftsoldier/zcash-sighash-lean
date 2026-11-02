/-
`zcash_primitives` 0.31.0's `Transaction::read` for version 5 and 6 transactions
(`src/transaction/mod.rs`, `src/transaction/components/{sapling,orchard}.rs`), and the readers it
calls in `zcash_transparent` 0.11.0 and `zcash_encoding` 0.5.0, under the default features (no
`zip-233`). A read error is `none`. An earlier version goes to `read_v4`, which is not
transcribed: `read` stops there (`.readV4`), where the crate reads on and may still fail. Zebra
and Zakura parse blocks with their own chain crates; this is the librustzcash reader, not theirs.

Checks that only reject more inputs are left out: that a byte string is a valid curve point or
field element (`read_value_commitment`, `read_rk`, `read_base`, `read_anchor`, ...), a valid
consensus branch (`BranchId::try_from`), Orchard flags valid for the bundle version
(`read_flags`), a value balance in range (`read_amount`), an Orchard bundle version for the
branch, and a canonical Orchard proof length (`try_from_parts`). So a version 5 or 6 transaction
this reader returns (`.tx`) is what `zcash_primitives` returns, and `Proofs/Read.lean` is about
what a successful read returns.
-/
module

public import ZcashSighash.Verifier.Parse

@[expose] public section

namespace ZcashSighash.Verifier.Read

open Spec (Byte Bytes)
open Native (Parser readBytes readLe fail readCount)

/-- `if cond { read } else { default }`, a value read only under a condition. -/
def readIf {α : Type} (cond : Bool) (read : Parser α) (default : α) : Parser α :=
  if cond then read else pure default

/-- `read_exact` into an `n`-byte array. -/
def readArr (n : ℕ) : Parser (Bytes n) := do
  let bytes ← readBytes n
  if h : bytes.length = n then pure ⟨bytes, h⟩ else fail

/-! ## `zcash_encoding` 0.5.0, `src/lib.rs` -/

/-- `CompactSize::read_unbounded` (lines 57–95): an error for a non-canonical encoding. -/
def readCompactSizeUnbounded : Parser ℕ := do
  let flag ← readLe 1
  if flag < 253 then pure flag
  else if flag = 253 then do
    let n ← readLe 2
    if n < 253 then fail else pure n
  else if flag = 254 then do
    let n ← readLe 4
    if n < 0x10000 then fail else pure n
  else do
    let n ← readLe 8
    if n < 0x100000000 then fail else pure n

/-- `CompactSize::read` (lines 40–48), and so `read_t` (lines 99–107), whose conversion to a
    `usize` cannot fail on a value at most `MAX_COMPACT_SIZE`. -/
def readCompactSize : Parser ℕ := do
  let n ← readCompactSizeUnbounded
  if n > MAX_COMPACT_SIZE then fail else pure n

/-- `Vector::read` (lines 167–172), through `read_collected_mut` (lines 185–194) and
    `Array::read_collected_mut` (lines 274–283). -/
def readVector {α : Type} (read : Parser α) : Parser (List α) := do
  let count ← readCompactSize
  readCount read count

/-! ## `zcash_transparent` 0.11.0 -/

/-- `Script::read` (`src/address.rs`, lines 60–66). -/
def readScript : Parser Transparent.Script := do
  let script ← readVector (BitVec.ofNat 8 <$> readLe 1)
  pure ⟨script⟩

/-- `OutPoint::read` (`src/bundle.rs`, lines 188–194). -/
def readOutPoint : Parser Transparent.OutPoint := do
  let hash ← readArr 32
  let n ← readLe 4
  pure ⟨hash, BitVec.ofNat 32 n⟩

/-- `TxIn::read` (lines 263–273). -/
def readTxIn : Parser Transparent.TxIn := do
  let prevout ← readOutPoint
  let scriptSig ← readScript
  let sequence ← readLe 4
  pure ⟨prevout, scriptSig, BitVec.ofNat 32 sequence⟩

/-- `TxOut::read` (lines 385–398), with `Zatoshis::from_nonnegative_i64_le_bytes`'s range
    check against `zcash_protocol` 0.11.0's `MAX_MONEY` (`src/value.rs`, lines 15–16), the same
    value as `Native.MAX_MONEY`. -/
def readTxOut : Parser Transparent.TxOut := do
  let value ← readLe 8
  if value > Native.MAX_MONEY then fail
  let scriptPubkey ← readScript
  pure ⟨BitVec.ofNat 64 value, scriptPubkey⟩

/-! ## `zcash_primitives` 0.31.0 -/

/-- `read_transparent` (`src/transaction/mod.rs`, lines 1066–1080), with the coins the inputs
    spend (`ctx`), which the transaction does not encode. -/
def readTransparent (ctx : Transparent.AuthorizingContext) :
    Parser (Option Transparent.Bundle) := do
  let vin ← readVector readTxIn
  let vout ← readVector readTxOut
  pure (if vin.isEmpty && vout.isEmpty then none else some ⟨vin, vout, ctx⟩)

/-- `read_amount` (lines 1082–1087): a `ZatBalance`, its `i64`. -/
def readAmount : Parser (BitVec 64) := do
  let bytes ← readLe 8
  pure (BitVec.ofNat 64 bytes)

/-- `read_spend_v5` (`src/transaction/components/sapling.rs`, lines 265–271): `cv`, the
    nullifier and `rk`. -/
def readSpendV5 : Parser (Bytes 32 × Bytes 32 × Bytes 32) := do
  let cv ← readArr 32
  let nullifier ← readArr 32
  let rk ← readArr 32
  pure (cv, nullifier, rk)

/-- `read_output_v5` (lines 344–366): `cv`, `cmu`, the ephemeral key and the ciphertexts. -/
def readOutputV5 : Parser (Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80) := do
  let cv ← readArr 32
  let cmu ← readArr 32
  let ephemeralKey ← readArr 32
  let encCiphertext ← readArr 580
  let outCiphertext ← readArr 80
  pure (cv, cmu, ephemeralKey, encCiphertext, outCiphertext)

/-- `Bundle::from_parts` (`sapling-crypto` 0.9.0, `src/bundle.rs`, lines 66–82): none without a
    Spend or an Output. -/
def saplingFromParts (spends : List Sapling.SpendDescription)
    (outputs : List Sapling.OutputDescription) (valueBalance : BitVec 64)
    (bindingSig : Bytes 64) : Option Sapling.Bundle :=
  if spends.isEmpty && outputs.isEmpty then none
  else some ⟨spends, outputs, valueBalance, bindingSig⟩

/-- `read_v5_bundle` (lines 450–504). The `anchor.unwrap()` cannot panic: it is reached only for
    a Spend, and with a Spend the anchor is read. -/
def readSaplingV5 : Parser (Option Sapling.Bundle) := do
  let sdV5s ← readVector readSpendV5
  let odV5s ← readVector readOutputV5
  let nSpends := sdV5s.length
  let nOutputs := odV5s.length
  let valueBalance ← readIf (nSpends > 0 || nOutputs > 0) readAmount 0
  let anchor ← readIf (nSpends > 0) (some <$> readArr 32) none
  let vSpendProofs ← readCount (readArr 192) nSpends
  let vSpendAuthSigs ← readCount (readArr 64) nSpends
  let vOutputProofs ← readCount (readArr 192) nOutputs
  let bindingSig ← readIf (nSpends > 0 || nOutputs > 0) (some <$> readArr 64) none
  let shieldedSpends := (sdV5s.zip (vSpendProofs.zip vSpendAuthSigs)).map
    fun ((cv, nullifier, rk), (zkproof, spendAuthSig)) =>
      (⟨cv, anchor.getD (List.Vector.replicate 32 0), nullifier, rk, zkproof, spendAuthSig⟩ :
        Sapling.SpendDescription)
  let shieldedOutputs := (odV5s.zip vOutputProofs).map
    fun ((cv, cmu, ephemeralKey, encCiphertext, outCiphertext), zkproof) =>
      (⟨cv, cmu, ephemeralKey, encCiphertext, outCiphertext, zkproof⟩ : Sapling.OutputDescription)
  pure (bindingSig.bind (saplingFromParts shieldedSpends shieldedOutputs valueBalance))

/-- `read_action_without_auth` (`src/transaction/components/orchard.rs`, lines 299–308):
    `cv_net`, the nullifier, `rk`, `cmx`, and the note ciphertext (lines 285–297). -/
def readActionWithoutAuth :
    Parser (Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 32 × Bytes 580 × Bytes 80) := do
  let cvNet ← readArr 32
  let nf ← readArr 32
  let rk ← readArr 32
  let cmx ← readArr 32
  let epkBytes ← readArr 32
  let encCiphertext ← readArr 580
  let outCiphertext ← readArr 80
  pure (cvNet, nf, rk, cmx, epkBytes, encCiphertext, outCiphertext)

/-- `NonEmpty::from_vec` (`nonempty` 0.11): none for an empty vector. -/
def nonEmptyFromVec {α : Type} : List α → Option (Orchard.NonEmpty α)
  | [] => none
  | a :: as => some ⟨a, as⟩

/-- `read_bundle` (lines 105–153), for the bundle slot of the value pool `pool`: the bundle
    version `bundle_version_for_branch` (lines 169–185) gives that slot is of that pool. The
    `NonEmpty::from_vec(...).expect(...)` cannot panic: there is a signature per action. -/
def readOrchardBundle (pool : Orchard.ValuePool) : Parser (Option Orchard.Bundle) := do
  let actionsWithoutAuth ← readVector readActionWithoutAuth
  if actionsWithoutAuth.isEmpty then pure none
  else
    let flags ← readLe 1
    let valueBalance ← readAmount
    let anchor ← readArr 32
    let proofBytes ← readVector (BitVec.ofNat 8 <$> readLe 1)
    let sigs ← readCount (readArr 64) actionsWithoutAuth.length
    let bindingSignature ← readArr 64
    let actions := (actionsWithoutAuth.zip sigs).map
      fun ((cvNet, nf, rk, cmx, epkBytes, encCiphertext, outCiphertext), sig) =>
        (⟨nf, rk, cmx, epkBytes, encCiphertext, outCiphertext, cvNet, sig⟩ : Orchard.Action)
    match nonEmptyFromVec actions with
    | none => fail
    | some actions => pure (some ⟨actions, BitVec.ofNat 8 flags, valueBalance, anchor, proofBytes,
        bindingSignature, pool⟩)

/-- `read_header_fragment` (`src/transaction/mod.rs`, lines 1151–1170): the consensus branch ID,
    the lock time and the expiry height. -/
def readHeaderFragment : Parser (BitVec 32 × BitVec 32 × BitVec 32) := do
  let consensusBranchId ← readLe 4
  let lockTime ← readLe 4
  let expiryHeight ← readLe 4
  pure (BitVec.ofNat 32 consensusBranchId, BitVec.ofNat 32 lockTime, BitVec.ofNat 32 expiryHeight)

/-- `read_v5` (lines 1089–1116), which `Transaction::read` (lines 973–986) calls for a version 5
    header. -/
def readV5 (ctx : Transparent.AuthorizingContext) : Parser TransactionData := do
  let (consensusBranchId, lockTime, expiryHeight) ← readHeaderFragment
  let transparentBundle ← readTransparent ctx
  let saplingBundle ← readSaplingV5
  let orchardBundle ← readOrchardBundle .orchard
  pure ⟨.v5, consensusBranchId, lockTime, expiryHeight, transparentBundle, none, saplingBundle,
    orchardBundle, none⟩

/-- `read_v6` (lines 1118–1149), which `Transaction::read` calls for a version 6 header. Its
    `read_v6_header_fragment` (lines 1172–1183) is `read_header_fragment` without `zip-233`. -/
def readV6 (ctx : Transparent.AuthorizingContext) : Parser TransactionData := do
  let (consensusBranchId, lockTime, expiryHeight) ← readHeaderFragment
  let transparentBundle ← readTransparent ctx
  let saplingBundle ← readSaplingV5
  let orchardBundle ← readOrchardBundle .orchard
  let ironwoodBundle ← readOrchardBundle .ironwood
  pure ⟨.v6, consensusBranchId, lockTime, expiryHeight, transparentBundle, none, saplingBundle,
    orchardBundle, ironwoodBundle⟩

/-- `TxVersion::read` (lines 89–115), without `V7`, with `V3_TX_VERSION` to `V6_TX_VERSION` and
    `V3_VERSION_GROUP_ID` to `V6_VERSION_GROUP_ID` (`zcash_protocol` 0.11.0, `src/constants.rs`,
    lines 16–42): an error for an unknown format. -/
def readTxVersion : Parser TxVersion := do
  let header ← readLe 4
  let overwintered := header >>> 31 = 1
  let version := header &&& 0x7FFFFFFF
  if overwintered then
    match version, ← readLe 4 with
    | 3, 0x03C48270 => pure .v3
    | 4, 0x892F2085 => pure .v4
    | 5, 0x26A7270A => pure .v5
    | 6, 0xD884B698 => pure .v6
    | _, _ => fail
  else if 1 ≤ version then pure (.sprout (BitVec.ofNat 32 version))
  else fail

/-- What `Transaction::read` does once it has read the version: read a version 5 or 6
    transaction, or hand an earlier one to `read_v4` (lines 989–1064), which is not transcribed. -/
inductive ReadOutcome where
  | tx (data : TransactionData)
  | readV4 (version : TxVersion)

/-- `Transaction::read` (lines 973–986), up to `read_v4`. The `HashReader` it reads through
    computes only `read_v4`'s identifier, and its `consensus_branch_id` goes only to `read_v4`, so
    both are left out. -/
def read (ctx : Transparent.AuthorizingContext) : Parser ReadOutcome := do
  let version ← readTxVersion
  match version with
  | .sprout _ | .v3 | .v4 => pure (.readV4 version)
  | .v5 => ReadOutcome.tx <$> readV5 ctx
  | .v6 => ReadOutcome.tx <$> readV6 ctx

end ZcashSighash.Verifier.Read
