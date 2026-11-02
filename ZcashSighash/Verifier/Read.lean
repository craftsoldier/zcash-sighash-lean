/-
`zcash_primitives` 0.31.0's `Transaction::read` (`src/transaction/mod.rs`,
`src/transaction/components/{sapling,orchard,sprout}.rs`), and the readers it calls in
`zcash_transparent` 0.11.0 and `zcash_encoding` 0.5.0, under the default features (no
`zip-233`). A read error is `none`. For a version before 5, the identifier is the SHA-256d of the
bytes read, which `read_v4` computes through a `HashReader`.

Zebra 7.0.0 parses every transaction, in blocks and from peers, with `Transaction::read`, which
this module transcribes: `zebra-chain` 15.0.0's `Transaction` wraps
`zcash_primitives`' (`src/transaction.rs`, line 59), and its `deserialize_and_check` (lines
902–1023), which both its deserializers go through, the one blocks use included
(`src/block/serialize.rs`, line 165), calls `Transaction::read` and then rejects more. Zakura
parses with its own chain crate (`Verifier/Parse.lean`).

Checks that only reject more inputs are left out: that a byte string is a valid curve point or
field element (`read_value_commitment`, `read_rk`, `read_base`, `read_anchor`, ...), a valid
consensus branch (`BranchId::try_from`), Orchard flags valid for the bundle version
(`read_flags`), an Orchard bundle version for the branch, and a canonical Orchard proof length
(`try_from_parts`). So every transaction `zcash_primitives` returns, this reader returns too.
`Proofs/Read.lean` is about what a successful read of a version 5 or 6 transaction returns, and
`Proofs/ReadV4.lean` about the identifier of a version 1 to 4 one.
-/
module

public import ZcashSighash.Verifier.Parse
public import ZcashSighash.Verifier.SighashV4
public import ZcashSighash.Verifier.Sha256

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

/-- `read_amount` (lines 1082–1087): a `ZatBalance`, its `i64`, through `from_i64_le_bytes` and
    `from_i64` (`zcash_protocol` 0.11.0, `src/value.rs`, lines 95–98 and 58–66): an error outside
    `-MAX_BALANCE..=MAX_BALANCE`, `MAX_BALANCE` being `MAX_MONEY` (lines 16–17), the same value
    as `Native.MAX_MONEY`. -/
def readAmount : Parser (BitVec 64) := do
  let bytes ← readLe 8
  let amount := BitVec.ofNat 64 bytes
  if -(Native.MAX_MONEY : ℤ) ≤ amount.toInt ∧ amount.toInt ≤ Native.MAX_MONEY then pure amount
  else fail

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
    header. `from_data_v5`'s `assert_eq!(data.version, TxVersion::V5)` (line 937) is left out:
    `Transaction::read` passes only `V5`. -/
def readV5 (ctx : Transparent.AuthorizingContext) (version : TxVersion) :
    Parser TransactionData := do
  let (consensusBranchId, lockTime, expiryHeight) ← readHeaderFragment
  let transparentBundle ← readTransparent ctx
  let saplingBundle ← readSaplingV5
  let orchardBundle ← readOrchardBundle .orchard
  pure ⟨version, consensusBranchId, lockTime, expiryHeight, transparentBundle, none,
    saplingBundle, orchardBundle, none⟩

/-- `read_v6` (lines 1118–1149), which `Transaction::read` calls for a version 6 header. Its
    `read_v6_header_fragment` (lines 1172–1183) is `read_header_fragment` without `zip-233`.
    `from_data_v6`'s `assert_eq!(data.version, TxVersion::V6)` (line 951) is left out:
    `Transaction::read` passes only `V6`. -/
def readV6 (ctx : Transparent.AuthorizingContext) (version : TxVersion) :
    Parser TransactionData := do
  let (consensusBranchId, lockTime, expiryHeight) ← readHeaderFragment
  let transparentBundle ← readTransparent ctx
  let saplingBundle ← readSaplingV5
  let orchardBundle ← readOrchardBundle .orchard
  let ironwoodBundle ← readOrchardBundle .ironwood
  pure ⟨version, consensusBranchId, lockTime, expiryHeight, transparentBundle, none,
    saplingBundle, orchardBundle, ironwoodBundle⟩

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

/-! ## Versions 1 to 4 -/

/-- `read_spend_v4` (`src/transaction/components/sapling.rs`, lines 223–245). -/
def readSpendV4 : Parser Sapling.SpendDescription := do
  let cv ← readArr 32
  let anchor ← readArr 32
  let nullifier ← readArr 32
  let rk ← readArr 32
  let zkproof ← readArr 192
  let spendAuthSig ← readArr 64
  pure ⟨cv, anchor, nullifier, rk, zkproof, spendAuthSig⟩

/-- `read_output_v4` (lines 280–311). -/
def readOutputV4 : Parser Sapling.OutputDescription := do
  let cv ← readArr 32
  let cmu ← readArr 32
  let ephemeralKey ← readArr 32
  let encCiphertext ← readArr 580
  let outCiphertext ← readArr 80
  let zkproof ← readArr 192
  pure ⟨cv, cmu, ephemeralKey, encCiphertext, outCiphertext, zkproof⟩

/-- `read_v4_components` (lines 384–404): the value balance, the Spends and the Outputs. -/
def readV4Components (txHasSapling : Bool) :
    Parser (BitVec 64 × List Sapling.SpendDescription × List Sapling.OutputDescription) :=
  if txHasSapling then do
    let vb ← readAmount
    let ss ← readVector readSpendV4
    let so ← readVector readOutputV4
    pure (vb, ss, so)
  else pure (0, [], [])

/-- `ZatBalance::from_u64_le_bytes` (`zcash_protocol` 0.11.0, `src/value.rs`, lines 111–114),
    through `from_u64` (lines 84–90): an error above `MAX_MONEY`. -/
def readU64Amount : Parser (BitVec 64) := do
  let amount ← readLe 8
  if amount ≤ Native.MAX_MONEY then pure (BitVec.ofNat 64 amount) else fail

/-- `JsDescription::read` (`src/transaction/components/sprout.rs`, lines 89–166): a Groth16
    proof (`GROTH_PROOF_SIZE`, 192 bytes) if `use_groth`, otherwise a BCTV14 one
    (`PHGR_PROOF_SIZE`, 296 bytes, line 10). -/
def readJsDescription (useGroth : Bool) : Parser Sprout.JsDescription := do
  let vpubOld ← readU64Amount
  let vpubNew ← readU64Amount
  let anchor ← readArr 32
  let nullifier₁ ← readArr 32
  let nullifier₂ ← readArr 32
  let commitment₁ ← readArr 32
  let commitment₂ ← readArr 32
  let ephemeralKey ← readArr 32
  let randomSeed ← readArr 32
  let mac₁ ← readArr 32
  let mac₂ ← readArr 32
  let proof ← if useGroth then Sprout.SproutProof.groth <$> readArr 192
    else Sprout.SproutProof.phgr <$> readArr 296
  let ciphertext₁ ← readArr 601
  let ciphertext₂ ← readArr 601
  pure ⟨vpubOld, vpubNew, anchor, (nullifier₁, nullifier₂), (commitment₁, commitment₂),
    ephemeralKey, randomSeed, (mac₁, mac₂), proof, (ciphertext₁, ciphertext₂)⟩

/-- `read_v4` (`src/transaction/mod.rs`, lines 989–1064), with `consensus_branch_id` as the
    transaction's branch ID. The identifier it takes from its `HashReader` is `read`'s. -/
def readV4 (ctx : Transparent.AuthorizingContext) (version : TxVersion)
    (consensusBranchId : BitVec 32) : Parser TransactionData := do
  let transparentBundle ← readTransparent ctx
  let lockTime ← readLe 4
  let expiryHeight ← if version.hasOverwinter then readLe 4 else pure 0
  let (valueBalance, shieldedSpends, shieldedOutputs) ← readV4Components version.hasSapling
  let sproutBundle ← if version.hasSprout then do
      let joinsplits ← readVector (readJsDescription version.hasSapling)
      if !joinsplits.isEmpty then do
        let joinsplitPubkey ← readArr 32
        let joinsplitSig ← readArr 64
        pure (some ⟨joinsplits, joinsplitPubkey, joinsplitSig⟩)
      else pure none
    else pure none
  let bindingSig ← if version.hasSapling && !(shieldedSpends.isEmpty && shieldedOutputs.isEmpty)
    then some <$> readArr 64 else pure none
  pure ⟨version, consensusBranchId, BitVec.ofNat 32 lockTime, BitVec.ofNat 32 expiryHeight,
    transparentBundle, sproutBundle,
    bindingSig.bind (saplingFromParts shieldedSpends shieldedOutputs valueBalance), none, none⟩

/-! ## `Transaction::read` -/

/-- `HashReader` (`zcash_transparent` 0.11.0, `src/util/sha256d.rs`, lines 4–39): `p`, and the
    bytes it read, which the `HashReader` hashes as they are read. -/
def hashReader {α : Type} (p : Parser α) : Parser (α × List Byte) := fun s =>
  (p s).map fun (a, s') => ((a, s.take (s.length - s'.length)), s')

/-- A transaction `Transaction::read` returns: one of version 5 or 6, whose identifier
    `from_data_v5` and `from_data_v6` compute from its data, or an earlier one with the
    identifier `read_v4` computes from the bytes it read. -/
inductive ReadOutcome where
  | tx (data : TransactionData)
  | v4 (data : TransactionData) (txid : List Byte)

/-- `Transaction::read` (lines 973–986), with `consensus_branch_id`, which only `read_v4` uses.
    Its `HashReader` hashes every byte it reads: the version's, then `read_v4`'s, whose
    `into_hash` (lines 1037–1039) gives the SHA-256d of them all. Versions 5 and 6 read on from the
    base reader. -/
def read (ctx : Transparent.AuthorizingContext) (consensusBranchId : BitVec 32) :
    Parser ReadOutcome := do
  let (version, header) ← hashReader readTxVersion
  match version with
  | .sprout _ | .v3 | .v4 => do
    let (data, body) ← hashReader (readV4 ctx version consensusBranchId)
    pure (.v4 data ((Sha256.sha256d ((header ++ body).map (·.toNat))).map (BitVec.ofNat 8)))
  | .v5 => ReadOutcome.tx <$> readV5 ctx version
  | .v6 => ReadOutcome.tx <$> readV6 ctx version

end ZcashSighash.Verifier.Read
