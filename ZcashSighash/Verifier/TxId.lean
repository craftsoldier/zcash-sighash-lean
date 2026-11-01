/-
`zcash_primitives` 0.31.0's transaction data (`src/transaction/mod.rs`) and its transaction
identifier and authorizing data digests (`src/transaction/txid.rs`). A `BranchId` is its `u32`,
and a `BlockHeight` its `u32`.
-/
module

public import ZcashSighash.Verifier.Transparent
public import ZcashSighash.Verifier.Shielded

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)

/-- `TxVersion` (`src/transaction/mod.rs`, lines 62–86), without `V7`, which only the
    `zcash_unstable = "nutachyon"` configuration has. -/
inductive TxVersion where
  | sprout (v : BitVec 32)
  | v3
  | v4
  | v5
  | v6

/-- `TxVersion::header` (lines 117–134), with `V3_TX_VERSION` to `V6_TX_VERSION` (3 to 6,
    `zcash_protocol` 0.11.0, `src/constants.rs`). -/
def TxVersion.header : TxVersion → BitVec 32
  | .sprout v => 0 ||| v
  | .v3 => (1 <<< 31) ||| 3
  | .v4 => (1 <<< 31) ||| 4
  | .v5 => (1 <<< 31) ||| 5
  | .v6 => (1 <<< 31) ||| 6

/-- `TxVersion::version_group_id` (lines 136–147), with `V3_VERSION_GROUP_ID` to
    `V6_VERSION_GROUP_ID` (`zcash_protocol` 0.11.0, `src/constants.rs`, lines 20, 30, 37 and
    42). -/
def TxVersion.versionGroupId : TxVersion → BitVec 32
  | .sprout _ => 0
  | .v3 => 0x03C48270
  | .v4 => 0x892F2085
  | .v5 => 0x26A7270A
  | .v6 => 0xD884B698

/-- `TxVersion::has_ironwood` (lines 196–203). -/
def TxVersion.hasIronwood : TxVersion → Bool
  | .v6 => true
  | _ => false

/-- `TransactionData<A>` (lines 339–352), without the Sprout bundle, which no version 5 or 6
    digest reads, and the `zip233_amount` of an unstable configuration. -/
structure TransactionData where
  version : TxVersion
  consensusBranchId : BitVec 32
  lockTime : BitVec 32
  expiryHeight : BitVec 32
  transparentBundle : Option Transparent.Bundle
  saplingBundle : Option Sapling.Bundle
  orchardBundle : Option Orchard.Bundle
  ironwoodBundle : Option Orchard.Bundle

/-- `TransparentDigests` (lines 1330–1334). -/
structure TransparentDigests where
  prevoutsDigest : Blake2bHash
  sequenceDigest : Blake2bHash
  outputsDigest : Blake2bHash

/-- `Zip244Digests` (lines 1374–1381). -/
structure Zip244Digests where
  headerDigest : Blake2bHash
  transparentDigests : Option TransparentDigests
  saplingDigest : Option Blake2bHash
  orchardDigest : Option Blake2bHash
  ironwoodDigest : Option Blake2bHash

/-! ## `src/transaction/txid.rs` -/

/-- `sapling_spends_noncompact_personalization` (lines 54–63). -/
def saplingSpendsNoncompactPersonalization : TxVersion → Bytes 16
  | .v6 => personal "ZTxIdSSpendNH_v6"
  | _ => personal "ZTxIdSSpendNHash"

/-- `sapling_auth_personalization` (lines 65–74). -/
def saplingAuthPersonalization : TxVersion → Bytes 16
  | .v6 => personal "ZTxAuthSapliH_v6"
  | _ => personal "ZTxAuthSapliHash"

/-- `sapling_auth_includes_anchor` (lines 76–83). -/
def saplingAuthIncludesAnchor : TxVersion → Bool
  | .v6 => true
  | _ => false

/-- `orchard_commitment_domain` (lines 90–99). -/
def orchardCommitmentDomain : TxVersion → Orchard.ValuePool × Orchard.TxVersion
  | .v6 => (.orchard, .v6)
  | _ => (.orchard, .v5)

/-- `ironwood_v6_domain` (lines 101–103). -/
def ironwoodV6Domain : Orchard.ValuePool × Orchard.TxVersion := (.ironwood, .v6)

/-- `transparent_prevout_hash` (lines 113–121). -/
def transparentPrevoutHash (vin : List Transparent.TxIn) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdPrevoutHash")
  for tIn in vin do
    h ← unwrap (tIn.prevout.write h)
  pure h.finalize

/-- `transparent_sequence_hash` (lines 125–133). -/
def transparentSequenceHash (vin : List Transparent.TxIn) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSequencHash")
  for tIn in vin do
    h ← unwrap (h.writeU32Le tIn.sequence)
  pure h.finalize

/-- `transparent_outputs_hash` (lines 139–145). -/
def transparentOutputsHash (vout : List Transparent.TxOut) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdOutputsHash")
  for tOut in vout do
    h ← unwrap (tOut.write h)
  pure h.finalize

/-- `hash_sapling_spends` (lines 158–189). -/
def hashSaplingSpends (version : TxVersion) (shieldedSpends : List Sapling.SpendDescription) :
    Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSSpendsHash")
  if !shieldedSpends.isEmpty then
    let mut ch ← hasher (personal "ZTxIdSSpendCHash")
    let mut nh ← hasher (saplingSpendsNoncompactPersonalization version)
    for sSpend in shieldedSpends do
      ch ← unwrap (ch.writeAll sSpend.nullifier.toList)
      nh ← unwrap (nh.writeAll sSpend.cv.toList)
      let writeAnchor := match version with
        | .v6 => false
        | _ => true
      if writeAnchor then
        nh ← unwrap (nh.writeAll sSpend.anchor.toList)
      nh ← unwrap (nh.writeAll sSpend.rk.toList)
    let compactDigest := ch.finalize
    h ← unwrap (h.writeAll compactDigest)
    let noncompactDigest := nh.finalize
    h ← unwrap (h.writeAll noncompactDigest)
  pure h.finalize

/-- `hash_sapling_outputs` (lines 199–222). -/
def hashSaplingOutputs (shieldedOutputs : List Sapling.OutputDescription) :
    Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSOutputHash")
  if !shieldedOutputs.isEmpty then
    let mut ch ← hasher (personal "ZTxIdSOutC__Hash")
    let mut mh ← hasher (personal "ZTxIdSOutM__Hash")
    let mut nh ← hasher (personal "ZTxIdSOutN__Hash")
    for sOut in shieldedOutputs do
      ch ← unwrap (ch.writeAll sOut.cmu.toList)
      ch ← unwrap (ch.writeAll sOut.ephemeralKey.toList)
      ch ← unwrap (ch.writeAll (sOut.encCiphertext.toList.take 52))
      mh ← unwrap (mh.writeAll ((sOut.encCiphertext.toList.drop 52).take (564 - 52)))
      nh ← unwrap (nh.writeAll sOut.cv.toList)
      nh ← unwrap (nh.writeAll (sOut.encCiphertext.toList.drop 564))
      nh ← unwrap (nh.writeAll sOut.outCiphertext.toList)
    h ← unwrap (h.writeAll ch.finalize)
    h ← unwrap (h.writeAll mh.finalize)
    h ← unwrap (h.writeAll nh.finalize)
  pure h.finalize

/-- `transparent_digests` (lines 226–234). -/
def transparentDigests (bundle : Transparent.Bundle) : Option TransparentDigests := do
  pure ⟨← transparentPrevoutHash bundle.vin, ← transparentSequenceHash bundle.vin,
    ← transparentOutputsHash bundle.vout⟩

/-- `hash_header_txid_data` (lines 237–253). -/
def hashHeaderTxidData (version : TxVersion) (consensusBranchId : BitVec 32)
    (lockTime : BitVec 32) (expiryHeight : BitVec 32) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdHeadersHash")
  h ← unwrap (h.writeU32Le version.header)
  h ← unwrap (h.writeU32Le version.versionGroupId)
  h ← unwrap (h.writeU32Le consensusBranchId)
  h ← unwrap (h.writeU32Le lockTime)
  h ← unwrap (h.writeU32Le expiryHeight)
  pure h.finalize

/-- `hash_transparent_txid_data` (lines 256–266). -/
def hashTransparentTxidData (tDigests : Option TransparentDigests) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdTranspaHash")
  if let some d := tDigests then
    h ← unwrap (h.writeAll d.prevoutsDigest)
    h ← unwrap (h.writeAll d.sequenceDigest)
    h ← unwrap (h.writeAll d.outputsDigest)
  pure h.finalize

/-- `hash_sapling_txid_data` (lines 271–287). -/
def hashSaplingTxidData (version : TxVersion) (bundle : Sapling.Bundle) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSaplingHash")
  if !(bundle.shieldedSpends.isEmpty && bundle.shieldedOutputs.isEmpty) then
    h ← unwrap (h.writeAll (← hashSaplingSpends version bundle.shieldedSpends))
    h ← unwrap (h.writeAll (← hashSaplingOutputs bundle.shieldedOutputs))
    h ← unwrap (h.writeAll (toLeBytes 8 bundle.valueBalance))
  pure h.finalize

/-- `hash_sapling_txid_empty` (lines 289–291). -/
def hashSaplingTxidEmpty : Option Blake2bHash := do
  pure (← hasher (personal "ZTxIdSaplingHash")).finalize

/-- `TxIdDigester::digest_orchard` (lines 340–351): the bundle's commitment, or a panic
    (`expect`) if its pool has no commitment format in the transaction's version. -/
def TxIdDigester.digestOrchard (version : TxVersion) (orchardBundle : Option Orchard.Bundle) :
    Option (Option Blake2bHash) :=
  match orchardBundle with
  | none => pure none
  | some b => do
    let (_, txVersion) := orchardCommitmentDomain version
    some <$> unwrap (← Orchard.hashBundleTxidData b txVersion)

/-- `TxIdDigester::digest_ironwood` (lines 353–363). -/
def TxIdDigester.digestIronwood (ironwoodBundle : Option Orchard.Bundle) :
    Option (Option Blake2bHash) :=
  match ironwoodBundle with
  | none => pure none
  | some b => do
    let (_, txVersion) := ironwoodV6Domain
    some <$> unwrap (← Orchard.hashBundleTxidData b txVersion)

/-- `TransactionData::digest` (`src/transaction/mod.rs`, lines 724–739) with `TxIdDigester`
    (`txid.rs`, lines 306–381): each component's digest, combined. -/
def TransactionData.txIdDigests (self : TransactionData) : Option Zip244Digests := do
  let headerDigest ← hashHeaderTxidData self.version self.consensusBranchId self.lockTime
    self.expiryHeight
  let transparentDigests ← match self.transparentBundle with
    | none => pure none
    | some b => some <$> transparentDigests b
  let saplingDigest ← match self.saplingBundle with
    | none => pure none
    | some b => some <$> hashSaplingTxidData self.version b
  let orchardDigest ← TxIdDigester.digestOrchard self.version self.orchardBundle
  let ironwoodDigest ← TxIdDigester.digestIronwood self.ironwoodBundle
  pure ⟨headerDigest, transparentDigests, saplingDigest, orchardDigest, ironwoodDigest⟩

/-- The personalization `prefix || CONSENSUS_BRANCH_ID` of `to_hash`, `to_hash_v6` and
    `BlockTxCommitmentDigester::combine`:

```rust
let mut personal = [0; 16];
personal[..12].copy_from_slice(PREFIX);
(&mut personal[12..]).write_u32_le(consensus_branch_id.into()).unwrap();
```

`write_u32_le` writes four bytes into the four left, so the `unwrap` cannot panic. -/
def branchPersonalization (pfx : Bytes 12) (consensusBranchId : BitVec 32) : Bytes 16 :=
  ⟨pfx.toList ++ toLeBytes 4 consensusBranchId, by simp [toLeBytes]⟩

/-- `to_hash` (lines 383–418). The empty Orchard digest's `expect` cannot panic: the pool is
    Orchard, which has a format in every version. -/
def toHash (txversion : TxVersion) (consensusBranchId : BitVec 32) (headerDigest : Blake2bHash)
    (transparentDigest : Blake2bHash) (saplingDigest orchardDigest : Option Blake2bHash) :
    Option Blake2bHash := do
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZcashTxHash_" 12) consensusBranchId)
  h ← unwrap (h.writeAll headerDigest)
  h ← unwrap (h.writeAll transparentDigest)
  h ← unwrap (h.writeAll (← match saplingDigest with
    | some d => pure d
    | none => hashSaplingTxidEmpty))
  h ← unwrap (h.writeAll (← match orchardDigest with
    | some d => pure d
    | none => do
      let (valuePool, txVersion) := orchardCommitmentDomain txversion
      unwrap (← Orchard.hashBundleTxidEmpty valuePool txVersion)))
  pure h.finalize

/-- `to_hash_v6` (lines 420–465). The empty digests' `expect`s cannot panic: Orchard and
    Ironwood both have a version 6 format. -/
def toHashV6 (consensusBranchId : BitVec 32) (headerDigest : Blake2bHash)
    (transparentDigest : Blake2bHash) (saplingDigest orchardDigest ironwoodDigest :
      Option Blake2bHash) : Option Blake2bHash := do
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZcashTxHash_" 12) consensusBranchId)
  h ← unwrap (h.writeAll headerDigest)
  h ← unwrap (h.writeAll transparentDigest)
  h ← unwrap (h.writeAll (← match saplingDigest with
    | some d => pure d
    | none => hashSaplingTxidEmpty))
  h ← unwrap (h.writeAll (← match orchardDigest with
    | some d => pure d
    | none => do
      let (valuePool, txVersion) := orchardCommitmentDomain .v6
      unwrap (← Orchard.hashBundleTxidEmpty valuePool txVersion)))
  h ← unwrap (h.writeAll (← match ironwoodDigest with
    | some d => pure d
    | none => do
      let (valuePool, txVersion) := ironwoodV6Domain
      unwrap (← Orchard.hashBundleTxidEmpty valuePool txVersion)))
  pure h.finalize

/-- `to_txid` (lines 474–512): `none` (the inner one) for a version before 5. The final
    `try_from(..).unwrap()` cannot panic: the digest has 32 bytes. -/
def toTxid (txversion : TxVersion) (consensusBranchId : BitVec 32) (digests : Zip244Digests) :
    Option (Option Blake2bHash) := do
  match txversion with
  | .sprout _ | .v3 | .v4 => pure none
  | .v5 | .v6 =>
    let txidDigest ← if txversion.hasIronwood then
      toHashV6 consensusBranchId digests.headerDigest
        (← hashTransparentTxidData digests.transparentDigests) digests.saplingDigest
        digests.orchardDigest digests.ironwoodDigest
    else
      toHash txversion consensusBranchId digests.headerDigest
        (← hashTransparentTxidData digests.transparentDigests) digests.saplingDigest
        digests.orchardDigest
    pure (some txidDigest)

/-! ## `BlockTxCommitmentDigester` (lines 518–649) -/

/-- `digest_transparent` (lines 542–553). -/
def BlockTxCommitmentDigester.digestTransparent
    (transparentBundle : Option Transparent.Bundle) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxAuthTransHash")
  if let some bundle := transparentBundle then
    for txin in bundle.vin do
      h ← unwrap (txin.scriptSig.write h)
  pure h.finalize

/-- `digest_sapling` (lines 555–584). Its `shielded_spends()[0]` cannot panic: it is read only
    when there is a spend. -/
def BlockTxCommitmentDigester.digestSapling (version : TxVersion)
    (saplingBundle : Option Sapling.Bundle) : Option Blake2bHash := do
  let mut h ← hasher (saplingAuthPersonalization version)
  if let some bundle := saplingBundle then
    for spend in bundle.shieldedSpends do
      h ← unwrap (h.writeAll spend.zkproof.toList)
    for spend in bundle.shieldedSpends do
      h ← unwrap (h.writeAll spend.spendAuthSig.toList)
    for output in bundle.shieldedOutputs do
      h ← unwrap (h.writeAll output.zkproof.toList)
    h ← unwrap (h.writeAll bundle.bindingSig.toList)
    if saplingAuthIncludesAnchor version && !bundle.shieldedSpends.isEmpty then
      if let some spend := bundle.shieldedSpends.head? then
        h ← unwrap (h.writeAll spend.anchor.toList)
  pure h.finalize

/-- `digest_orchard` (lines 586–603): a panic (`expect`) if the bundle's pool has no format in
    the transaction's version. -/
def BlockTxCommitmentDigester.digestOrchard (version : TxVersion)
    (orchardBundle : Option Orchard.Bundle) : Option Blake2bHash := do
  let (valuePool, txVersion) := orchardCommitmentDomain version
  match orchardBundle with
  | none => unwrap (← Orchard.hashBundleAuthEmpty valuePool txVersion)
  | some b => unwrap (← Orchard.hashBundleAuthData b txVersion)

/-- `digest_ironwood` (lines 605–621). -/
def BlockTxCommitmentDigester.digestIronwood (ironwoodBundle : Option Orchard.Bundle) :
    Option Blake2bHash := do
  let (valuePool, txVersion) := ironwoodV6Domain
  match ironwoodBundle with
  | none => unwrap (← Orchard.hashBundleAuthEmpty valuePool txVersion)
  | some b => unwrap (← Orchard.hashBundleAuthData b txVersion)

/-- `TransactionData::digest` with `BlockTxCommitmentDigester`, through its `combine` (lines
    623–648): `Transaction::auth_commitment` (`src/transaction/mod.rs`, lines 1317–1319). -/
def TransactionData.authCommitment (self : TransactionData) : Option Blake2bHash := do
  let transparentDigest ← BlockTxCommitmentDigester.digestTransparent self.transparentBundle
  let saplingDigest ← BlockTxCommitmentDigester.digestSapling self.version self.saplingBundle
  let orchardDigest ← BlockTxCommitmentDigester.digestOrchard self.version self.orchardBundle
  let ironwoodDigest ← BlockTxCommitmentDigester.digestIronwood self.ironwoodBundle
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZTxAuthHash_" 12)
    self.consensusBranchId)
  h ← unwrap (h.writeAll transparentDigest)
  h ← unwrap (h.writeAll saplingDigest)
  h ← unwrap (h.writeAll orchardDigest)
  if self.version.hasIronwood then
    h ← unwrap (h.writeAll ironwoodDigest)
  pure h.finalize

end ZcashSighash.Verifier
