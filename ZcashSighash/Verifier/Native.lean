/-
Zakura's own ZIP 244 / ZIP 229 digests, which its node uses to validate version 5 and 6
transactions instead of `zakura-primitives`: `zakura-chain` 10.0.0, `src/transaction/zip244.rs`,
over its parsed transaction types (`src/transparent.rs`, `src/sapling/shielded_data.rs`,
`src/orchard/shielded_data.rs`) and their serializers (`src/serialization/`).

The types keep their invariants by construction, as the Rust's do: a Sapling component has a
Spend or an Output, and an Orchard-shaped one has an Action. A coinbase input holds its height
and data; `coinbase_script` rebuilds its `scriptSig` with `zcash_script`'s `push_num`. Here that is
a parameter (`CoinbaseScript`), so the digest theorems hold whatever it computes; Zakura's is
`CoinbaseScript.zakura` (`Verifier/Parse.lean`).
-/
module

public import ZcashSighash.Verifier.TxId
public import ZcashSighash.Verifier.Script

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes personal)
open Orchard (update finalize)

/-! ## Serialization (`src/serialization/`) -/

/-- `MAX_PROTOCOL_MESSAGE_LEN` (`zcash_serialize.rs`, line 11). -/
def MAX_PROTOCOL_MESSAGE_LEN : ℕ := 2 * 1024 * 1024

/-- `CompactSize64::zcash_serialize` (`compact_size.rs`, lines 334–361). -/
def compactSize64 (n : ℕ) : List Byte :=
  if n ≤ 0xfc then [BitVec.ofNat 8 n]
  else if n ≤ 0xffff then 0xfd :: toLeBytes 2 (BitVec.ofNat 16 n)
  else if n ≤ 0xffffffff then 0xfe :: toLeBytes 4 (BitVec.ofNat 32 n)
  else 0xff :: toLeBytes 8 (BitVec.ofNat 64 n)

/-- `zcash_serialize_bytes` (`zcash_serialize.rs`, lines 147–154), through
    `CompactSizeMessage::try_from` (`compact_size.rs`, lines 233–256): an error for a length
    that does not fit in a `u32` or exceeds `MAX_PROTOCOL_MESSAGE_LEN`. -/
def serializeBytes (v : List Byte) : Except Unit (List Byte) :=
  if 2 ^ 32 ≤ v.length then .error ()
  else if v.length > MAX_PROTOCOL_MESSAGE_LEN then .error ()
  else .ok (compactSize64 v.length ++ v)

/-- `update_serialized` (`zip244.rs`, lines 181–185): a panic if serializing fails. -/
def updateSerialized (state : Blake2b.State) (bytes : Except Unit (List Byte)) :
    Option Blake2b.State :=
  match bytes with
  | .ok b => some (update state b)
  | .error _ => none

/-! ## Transparent (`src/transparent.rs`) -/

/-- `OutPoint` (lines 68–82). -/
structure OutPoint where
  hash : Bytes 32
  index : BitVec 32

/-- `OutPoint::zcash_serialize` (`transparent/serialize.rs`, lines 98–104). -/
def OutPoint.serialize (o : OutPoint) : List Byte := o.hash.toList ++ toLeBytes 4 o.index

/-- `Input` (lines 103–123). A coinbase input's height is a `block::Height`, a `u32`. -/
inductive Input where
  | prevOut (outpoint : OutPoint) (unlockScript : List Byte) (sequence : BitVec 32)
  | coinbase (height : BitVec 32) (data : List Byte) (sequence : BitVec 32)

/-- `Input::sequence` (lines 191–195). -/
def Input.sequence : Input → BitVec 32
  | .prevOut _ _ s | .coinbase _ _ s => s

/-- `zcash_script`'s `push_num(height).to_bytes()` and the genesis coinbase `scriptSig`
    (`GENESIS_COINBASE_SCRIPT_SIG`, `transparent/serialize.rs`, line 24), which
    `Input::coinbase_script` reads. -/
structure CoinbaseScript where
  pushNum : BitVec 32 → List Byte
  genesis : List Byte

/-- `Input::coinbase_script` (lines 173–188). `Height::MIN` is 0. -/
def Input.coinbaseScript (cs : CoinbaseScript) : Input → Option (List Byte)
  | .prevOut .. => none
  | .coinbase height data _ =>
    if height = 0 then if data = cs.genesis then some cs.genesis else none
    else some (cs.pushNum height ++ data)

/-- `Output` (lines 317–324): an `Amount<NonNegative>` is its `i64`. -/
structure Output where
  value : BitVec 64
  lockScript : List Byte

/-- `Output::zcash_serialize` (`transparent/serialize.rs`, lines 229–235). -/
def Output.serialize (o : Output) : Except Unit (List Byte) := do
  pure (toLeBytes 8 o.value ++ (← serializeBytes o.lockScript))

/-! ## Sapling (`src/sapling/shielded_data.rs`) and Orchard (`src/orchard/shielded_data.rs`) -/

/-- A Sapling `Spend<SharedAnchor>`, its fields as their encodings. -/
structure SaplingSpend where
  cv : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  zkproof : Bytes 192
  spendAuthSig : Bytes 64

/-- A Sapling `Output`, its fields as their encodings. -/
structure SaplingOutput where
  cv : Bytes 32
  cmu : Bytes 32
  ephemeralKey : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  zkproof : Bytes 192

/-- `TransferData<SharedAnchor>` (lines 124–173): Spends with their shared anchor and maybe
    Outputs, or just Outputs. -/
inductive SaplingTransfers where
  | spendsAndMaybeOutputs (sharedAnchor : Bytes 32) (spends : Orchard.NonEmpty SaplingSpend)
      (maybeOutputs : List SaplingOutput)
  | justOutputs (outputs : Orchard.NonEmpty SaplingOutput)

/-- `ShieldedData<SharedAnchor>` (lines 90–111). -/
structure SaplingData where
  valueBalance : BitVec 64
  transfers : SaplingTransfers
  bindingSig : Bytes 64

/-- `ShieldedData::spends` (lines 258–260), through `TransferData::spends` (lines 388–399). -/
def SaplingData.spends (s : SaplingData) : List SaplingSpend :=
  match s.transfers with
  | .spendsAndMaybeOutputs _ spends _ => spends.toList
  | .justOutputs _ => []

/-- `ShieldedData::outputs` (lines 264–266), through `TransferData::outputs` (lines 402–410). -/
def SaplingData.outputs (s : SaplingData) : List SaplingOutput :=
  match s.transfers with
  | .spendsAndMaybeOutputs _ _ maybeOutputs => maybeOutputs
  | .justOutputs outputs => outputs.toList

/-- `ShieldedData::shared_anchor` (lines 290–292). -/
def SaplingData.sharedAnchor (s : SaplingData) : Option (Bytes 32) :=
  match s.transfers with
  | .spendsAndMaybeOutputs a _ _ => some a
  | .justOutputs _ => none

/-- An Orchard `AuthorizedAction`, its fields as their encodings. -/
structure Action where
  cv : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  cmx : Bytes 32
  ephemeralKey : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  spendAuthSig : Bytes 64

/-- Orchard's `ShieldedData` (lines 40–59), also Ironwood's. -/
structure OrchardData where
  flags : Byte
  valueBalance : BitVec 64
  sharedAnchor : Bytes 32
  proof : List Byte
  actions : Orchard.NonEmpty Action
  bindingSig : Bytes 64

/-! ## `src/transaction/zip244.rs`

The digests of empty components are written in as constants; `Proofs/Native.lean` proves each
is the BLAKE2b-256 hash of no bytes under its personalization. -/

/-- `EMPTY_TRANSPARENT_TXID_HASH` (line 97). -/
def EMPTY_TRANSPARENT_TXID_HASH : Blake2bHash :=
  [0xc3, 0x3f, 0x2e, 0x95, 0x70, 0x5f, 0xaa, 0xb3, 0x5f, 0x8d, 0x53, 0x3f, 0xa6, 0x1e, 0x95,
  0xc3, 0xb7, 0xaa, 0xba, 0x07, 0x76, 0xb8, 0x74, 0xa9, 0xf7, 0x4f, 0xc1, 0x27, 0x84, 0x37,
  0x6a, 0x59]

/-- `EMPTY_SAPLING_TXID_HASH` (line 101). -/
def EMPTY_SAPLING_TXID_HASH : Blake2bHash :=
  [0x6f, 0x2f, 0xc8, 0xf9, 0x8f, 0xea, 0xfd, 0x94, 0xe7, 0x4a, 0x0d, 0xf4, 0xbe, 0xd7, 0x43,
  0x91, 0xee, 0x0b, 0x5a, 0x69, 0x94, 0x5e, 0x4c, 0xed, 0x8c, 0xa8, 0xa0, 0x95, 0x20, 0x6f,
  0x00, 0xae]

/-- `EMPTY_SAPLING_SPENDS_HASH` (line 105). -/
def EMPTY_SAPLING_SPENDS_HASH : Blake2bHash :=
  [0xd7, 0x9c, 0x8d, 0xcb, 0x8a, 0xf4, 0x6b, 0xd8, 0x0f, 0xe3, 0xbc, 0xdc, 0x0e, 0x5d, 0x0e,
  0xd7, 0x34, 0x4d, 0x5f, 0x48, 0xcb, 0xef, 0xf3, 0xc9, 0x4b, 0x13, 0xd4, 0x0a, 0x23, 0x05,
  0xf8, 0x4d]

/-- `EMPTY_SAPLING_OUTPUTS_HASH` (line 109). -/
def EMPTY_SAPLING_OUTPUTS_HASH : Blake2bHash :=
  [0x9e, 0x28, 0xee, 0xf8, 0xdf, 0x6f, 0xcc, 0x96, 0x68, 0xef, 0x92, 0xfc, 0xdc, 0x41, 0x2f,
  0xc5, 0xb6, 0xd7, 0x03, 0x7e, 0xf1, 0xf9, 0x63, 0x76, 0x7b, 0xd7, 0xb8, 0x01, 0x12, 0x67,
  0xbf, 0x95]

/-- `EMPTY_ORCHARD_V5_TXID_HASH` (line 113). -/
def EMPTY_ORCHARD_V5_TXID_HASH : Blake2bHash :=
  [0x9f, 0xbe, 0x4e, 0xd1, 0x3b, 0x0c, 0x08, 0xe6, 0x71, 0xc1, 0x1a, 0x34, 0x07, 0xd8, 0x4e,
  0x11, 0x17, 0xcd, 0x45, 0x02, 0x8a, 0x2e, 0xee, 0x1b, 0x9f, 0xea, 0xe7, 0x8b, 0x48, 0xa6,
  0xe2, 0xc1]

/-- `EMPTY_ORCHARD_V6_TXID_HASH` (line 117). -/
def EMPTY_ORCHARD_V6_TXID_HASH : Blake2bHash :=
  [0xa3, 0x36, 0x7d, 0x2f, 0xde, 0xa2, 0x91, 0x01, 0x59, 0xfc, 0x50, 0x26, 0xe9, 0xbf, 0x1f,
  0xcc, 0xd3, 0xe2, 0x8c, 0xe5, 0xe6, 0xde, 0x46, 0xbf, 0xb7, 0x15, 0x87, 0x23, 0x0e, 0xea,
  0x95, 0x15]

/-- `EMPTY_IRONWOOD_TXID_HASH` (line 121). -/
def EMPTY_IRONWOOD_TXID_HASH : Blake2bHash :=
  [0xb9, 0xcf, 0xe6, 0x43, 0xce, 0x45, 0xb2, 0x8c, 0x33, 0x19, 0x0f, 0x0d, 0x52, 0x23, 0xe4,
  0x75, 0x97, 0x2f, 0x2a, 0x14, 0x9d, 0xc5, 0x44, 0x04, 0xfd, 0x83, 0x65, 0x52, 0x1f, 0x84,
  0x16, 0xc5]

/-- `EMPTY_TRANSPARENT_AUTH_HASH` (line 125). -/
def EMPTY_TRANSPARENT_AUTH_HASH : Blake2bHash :=
  [0xe9, 0x88, 0x2b, 0xce, 0x1c, 0xf1, 0x35, 0x69, 0x02, 0xc6, 0xe2, 0x58, 0xc5, 0x67, 0xeb,
  0xc0, 0xd9, 0x92, 0x88, 0x67, 0xde, 0x9a, 0x35, 0x89, 0xbb, 0xbd, 0x31, 0x0e, 0xb6, 0x89,
  0x04, 0xe5]

/-- `EMPTY_SAPLING_V5_AUTH_HASH` (line 129). -/
def EMPTY_SAPLING_V5_AUTH_HASH : Blake2bHash :=
  [0xd2, 0x25, 0x67, 0x30, 0x66, 0xb0, 0xcd, 0x76, 0xa7, 0x71, 0x51, 0xbf, 0x05, 0x6d, 0x57,
  0x77, 0x92, 0xf3, 0x57, 0x73, 0x91, 0x20, 0x8d, 0x4c, 0xec, 0x25, 0x31, 0x8a, 0x8d, 0x5c,
  0xd9, 0x6f]

/-- `EMPTY_SAPLING_V6_AUTH_HASH` (line 133). -/
def EMPTY_SAPLING_V6_AUTH_HASH : Blake2bHash :=
  [0x0e, 0xe4, 0xb9, 0x56, 0x0b, 0xae, 0x42, 0x30, 0xa9, 0x9b, 0xfa, 0x52, 0x8e, 0x0a, 0x6a,
  0xab, 0xc7, 0xe2, 0x53, 0x86, 0xf3, 0x66, 0x59, 0x97, 0x67, 0xe7, 0xca, 0x10, 0x7b, 0x8c,
  0x17, 0x46]

/-- `EMPTY_ORCHARD_V5_AUTH_HASH` (line 137). -/
def EMPTY_ORCHARD_V5_AUTH_HASH : Blake2bHash :=
  [0x14, 0xed, 0xaa, 0x1e, 0x66, 0x9a, 0x63, 0xa8, 0x00, 0xbf, 0xe0, 0xb8, 0xfc, 0xd3, 0xd1,
  0x0e, 0x36, 0x81, 0x11, 0x5b, 0xee, 0x03, 0x25, 0x3d, 0xa0, 0x2e, 0x09, 0x80, 0x42, 0xd9,
  0xff, 0x90]

/-- `EMPTY_ORCHARD_V6_AUTH_HASH` (line 141). -/
def EMPTY_ORCHARD_V6_AUTH_HASH : Blake2bHash :=
  [0x79, 0x8e, 0x7f, 0xcd, 0x05, 0xbb, 0x7b, 0x7e, 0x9e, 0x49, 0x42, 0x4b, 0xdd, 0xe7, 0x68,
  0xa5, 0x00, 0xb6, 0x6f, 0xf2, 0x3d, 0x75, 0x9b, 0x87, 0x7d, 0x07, 0x54, 0xe3, 0xff, 0x79,
  0x7d, 0x91]

/-- `EMPTY_IRONWOOD_AUTH_HASH` (line 145). -/
def EMPTY_IRONWOOD_AUTH_HASH : Blake2bHash :=
  [0xec, 0x97, 0x68, 0xfd, 0xaa, 0x11, 0xf1, 0x2c, 0xdb, 0x13, 0xf5, 0x66, 0xb5, 0x95, 0x84,
  0x3f, 0x3d, 0x0e, 0x92, 0xb6, 0x70, 0x3e, 0xaf, 0xff, 0x17, 0x2e, 0x21, 0x34, 0x5b, 0x58,
  0x61, 0x33]

/-- `hasher` (lines 151–153): `Params::new().hash_length(32).personal(personal).to_state()`. -/
def hasher (personal : Bytes 16) : Option Blake2b.State := Orchard.hasher personal

/-- `Zip244Version` (lines 188–191). -/
inductive Version where
  | v5
  | v6

/-- `Zip244Parts` (lines 343–353), with `network_upgrade`'s branch ID (`consensus_branch_id`,
    lines 377–385), `raw_lock_time`, and `expiry_height().unwrap_or(0)`: the expiry height,
    which `expiry_height` maps to `None` exactly when it is 0. -/
structure Parts where
  version : Version
  consensusBranchId : BitVec 32
  lockTime : BitVec 32
  expiryHeight : BitVec 32
  inputs : List Input
  outputs : List Output
  sapling : Option SaplingData
  orchard : Option OrchardData
  ironwood : Option OrchardData

/-- `Zip244Version::header` (lines 194–200). -/
def Version.header : Version → BitVec 32
  | .v5 => (1 <<< 31) ||| 5
  | .v6 => (1 <<< 31) ||| 6

/-- `Zip244Version::version_group_id` (lines 202–207), with `TX_V5_VERSION_GROUP_ID` and
    `TX_V6_VERSION_GROUP_ID` (`src/parameters/transaction.rs`, lines 13 and 16). -/
def Version.versionGroupId : Version → BitVec 32
  | .v5 => 0x26A7270A
  | .v6 => 0xD884B698

/-- `hash_header` (lines 392–400). -/
def hashHeader (p : Parts) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdHeadersHash")
  h := update h (toLeBytes 4 p.version.header)
  h := update h (toLeBytes 4 p.version.versionGroupId)
  h := update h (toLeBytes 4 p.consensusBranchId)
  h := update h (toLeBytes 4 p.lockTime)
  h := update h (toLeBytes 4 p.expiryHeight)
  pure (finalize h)

/-- `hash_prevouts` (lines 407–421): a coinbase input as the null outpoint. -/
def hashPrevouts (inputs : List Input) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdPrevoutHash")
  for input in inputs do
    match input with
    | .prevOut outpoint _ _ => h ← updateSerialized h (.ok outpoint.serialize)
    | .coinbase .. =>
      h := update h (List.replicate 32 0)
      h := update h (toLeBytes 4 (0xffffffff : BitVec 32))
  pure (finalize h)

/-- `hash_sequence` (lines 427–433). -/
def hashSequence (inputs : List Input) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSequencHash")
  for input in inputs do
    h := update h (toLeBytes 4 input.sequence)
  pure (finalize h)

/-- `hash_outputs` (lines 439–445). -/
def hashOutputs (outputs : List Output) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdOutputsHash")
  for output in outputs do
    h ← updateSerialized h output.serialize
  pure (finalize h)

/-- `hash_amounts` (lines 448–454). -/
def hashAmounts (previousOutputs : List Output) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxTrAmountsHash")
  for output in previousOutputs do
    h := update h (toLeBytes 8 output.value)
  pure (finalize h)

/-- `hash_scriptpubkeys` (lines 457–463). -/
def hashScriptpubkeys (previousOutputs : List Output) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxTrScriptsHash")
  for output in previousOutputs do
    h ← updateSerialized h (serializeBytes output.lockScript)
  pure (finalize h)

/-- `hash_txin` (lines 466–483): `None` (the inner one) for a coinbase input. -/
def hashTxin (input : Input) (previousOutput : Output) : Option (Option Blake2bHash) := do
  match input with
  | .coinbase .. => pure none
  | .prevOut outpoint _ sequence =>
    let mut h ← hasher (personal "Zcash___TxInHash")
    h ← updateSerialized h (.ok outpoint.serialize)
    h := update h (toLeBytes 8 previousOutput.value)
    h ← updateSerialized h (serializeBytes previousOutput.lockScript)
    h := update h (toLeBytes 4 sequence)
    pure (some (finalize h))

/-- `hash_transparent_txid_from_digests` (lines 485–500). -/
def hashTransparentTxidFromDigests (bundlePresent : Bool)
    (prevouts sequence outputs : Blake2bHash) : Option Blake2bHash := do
  if !bundlePresent then return EMPTY_TRANSPARENT_TXID_HASH
  let mut h ← hasher (personal "ZTxIdTranspaHash")
  h := update h prevouts
  h := update h sequence
  h := update h outputs
  pure (finalize h)

/-- `hash_transparent_txid` (lines 506–520). -/
def hashTransparentTxid (inputs : List Input) (outputs : List Output) : Option Blake2bHash := do
  if inputs.isEmpty && outputs.isEmpty then return EMPTY_TRANSPARENT_TXID_HASH
  hashTransparentTxidFromDigests true (← hashPrevouts inputs) (← hashSequence inputs)
    (← hashOutputs outputs)

/-- `Zip244Version::sapling_spends_noncompact_personalization` (lines 209–214). -/
def Version.saplingSpendsNoncompactPersonalization : Version → Bytes 16
  | .v5 => personal "ZTxIdSSpendNHash"
  | .v6 => personal "ZTxIdSSpendNH_v6"

/-- `Zip244Version::sapling_spends_txid_includes_anchor` (lines 216–221). -/
def Version.saplingSpendsTxidIncludesAnchor : Version → Bool
  | .v5 => true
  | .v6 => false

/-- `hash_sapling_spends` (lines 526–554): the anchor's `expect` panics without a shared
    anchor. -/
def hashSaplingSpends (sapling : SaplingData) (version : Version) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSSpendsHash")
  if !sapling.spends.isEmpty then
    let mut ch ← hasher (personal "ZTxIdSSpendCHash")
    let mut nh ← hasher version.saplingSpendsNoncompactPersonalization
    let anchor ← if version.saplingSpendsTxidIncludesAnchor then
        some <$> sapling.sharedAnchor
      else pure none
    for spend in sapling.spends do
      ch := update ch spend.nullifier.toList
      nh := update nh spend.cv.toList
      if let some anchor := anchor then
        nh := update nh anchor.toList
      nh := update nh spend.rk.toList
    h := update h (finalize ch)
    h := update h (finalize nh)
  pure (finalize h)

/-- `hash_sapling_outputs` (lines 560–582). -/
def hashSaplingOutputs (sapling : SaplingData) : Option Blake2bHash := do
  let mut h ← hasher (personal "ZTxIdSOutputHash")
  if !sapling.outputs.isEmpty then
    let mut ch ← hasher (personal "ZTxIdSOutC__Hash")
    let mut mh ← hasher (personal "ZTxIdSOutM__Hash")
    let mut nh ← hasher (personal "ZTxIdSOutN__Hash")
    for output in sapling.outputs do
      ch := update ch output.cmu.toList
      ch := update ch output.ephemeralKey.toList
      ch := update ch (output.encCiphertext.toList.take 52)
      mh := update mh ((output.encCiphertext.toList.drop 52).take (564 - 52))
      nh := update nh output.cv.toList
      nh := update nh (output.encCiphertext.toList.drop 564)
      nh := update nh output.outCiphertext.toList
    h := update h (finalize ch)
    h := update h (finalize mh)
    h := update h (finalize nh)
  pure (finalize h)

/-- `hash_sapling_txid` (lines 588–611). -/
def hashSaplingTxid (sapling : Option SaplingData) (version : Version) : Option Blake2bHash := do
  let some sapling := sapling | return EMPTY_SAPLING_TXID_HASH
  let mut h ← hasher (personal "ZTxIdSaplingHash")
  if !sapling.spends.isEmpty then h := update h (← hashSaplingSpends sapling version)
  else h := update h EMPTY_SAPLING_SPENDS_HASH
  if !sapling.outputs.isEmpty then h := update h (← hashSaplingOutputs sapling)
  else h := update h EMPTY_SAPLING_OUTPUTS_HASH
  h := update h (toLeBytes 8 sapling.valueBalance)
  pure (finalize h)

/-- `BundleCommitmentFormat` (lines 293–297). -/
inductive Format where
  | orchardV5
  | orchardV6
  | ironwoodV6

/-- `BundleCommitmentFormat::personalizations` (lines 300–306), with
    `ORCHARD_V5_PERSONALIZATIONS`, `ORCHARD_V6_PERSONALIZATIONS` and
    `IRONWOOD_V6_PERSONALIZATIONS` (lines 265–290). -/
def Format.personalizations : Format → Orchard.Personalizations
  | .orchardV5 => ⟨personal "ZTxIdOrchardHash", personal "ZTxIdOrcActCHash",
      personal "ZTxIdOrcActMHash", personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaHash"⟩
  | .orchardV6 => ⟨personal "ZTxIdOrchardH_v6", personal "ZTxIdOrcActCHash",
      personal "ZTxIdOrcActMHash", personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaH_v6"⟩
  | .ironwoodV6 => ⟨personal "ZTxIdIronwd_H_v6", personal "ZTxIdIrnActCH_v6",
      personal "ZTxIdIrnActMH_v6", personal "ZTxIdIrnActNH_v6", personal "ZTxAuthIrnwdH_v6"⟩

/-- `BundleCommitmentFormat::includes_anchor_in_txid_digest` (lines 308–313). -/
def Format.includesAnchorInTxidDigest : Format → Bool
  | .orchardV5 => true
  | .orchardV6 | .ironwoodV6 => false

/-- `BundleCommitmentFormat::includes_anchor_in_authorizing_digest` (lines 315–320). -/
def Format.includesAnchorInAuthorizingDigest : Format → Bool
  | .orchardV5 => false
  | .orchardV6 | .ironwoodV6 => true

/-- `BundleCommitmentFormat::empty_txid_hash` (lines 322–328). -/
def Format.emptyTxidHash : Format → Blake2bHash
  | .orchardV5 => EMPTY_ORCHARD_V5_TXID_HASH
  | .orchardV6 => EMPTY_ORCHARD_V6_TXID_HASH
  | .ironwoodV6 => EMPTY_IRONWOOD_TXID_HASH

/-- `BundleCommitmentFormat::empty_auth_hash` (lines 330–336). -/
def Format.emptyAuthHash : Format → Blake2bHash
  | .orchardV5 => EMPTY_ORCHARD_V5_AUTH_HASH
  | .orchardV6 => EMPTY_ORCHARD_V6_AUTH_HASH
  | .ironwoodV6 => EMPTY_IRONWOOD_AUTH_HASH

/-- `Zip244Version::orchard_format` (lines 244–249). -/
def Version.orchardFormat : Version → Format
  | .v5 => .orchardV5
  | .v6 => .orchardV6

/-- `Zip244Version::has_ironwood` (lines 251–253). -/
def Version.hasIronwood : Version → Bool
  | .v5 => false
  | .v6 => true

/-- `hash_bundle_txid` (lines 616–651). -/
def hashBundleTxid (bundle : Option OrchardData) (format : Format) : Option Blake2bHash := do
  let some bundle := bundle | return format.emptyTxidHash
  let personalizations := format.personalizations
  let mut h ← hasher personalizations.bundle
  let mut ch ← hasher personalizations.actionsCompact
  let mut mh ← hasher personalizations.actionsMemos
  let mut nh ← hasher personalizations.actionsNoncompact
  for action in bundle.actions.toList do
    ch := update ch action.nullifier.toList
    ch := update ch action.cmx.toList
    ch := update ch action.ephemeralKey.toList
    ch := update ch (action.encCiphertext.toList.take 52)
    mh := update mh ((action.encCiphertext.toList.drop 52).take (564 - 52))
    nh := update nh action.cv.toList
    nh := update nh action.rk.toList
    nh := update nh (action.encCiphertext.toList.drop 564)
    nh := update nh action.outCiphertext.toList
  h := update h (finalize ch)
  h := update h (finalize mh)
  h := update h (finalize nh)
  h := update h [bundle.flags]
  h := update h (toLeBytes 8 bundle.valueBalance)
  if format.includesAnchorInTxidDigest then
    h := update h bundle.sharedAnchor.toList
  pure (finalize h)

/-- `combine_txid_digests` (lines 657–680). -/
def combineTxidDigests (consensusBranchId : BitVec 32)
    (header transparent sapling orchard : Blake2bHash) (ironwood : Option Blake2bHash) :
    Option Blake2bHash := do
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZcashTxHash_" 12) consensusBranchId)
  h := update h header
  h := update h transparent
  h := update h sapling
  h := update h orchard
  if let some ironwood := ironwood then
    h := update h ironwood
  pure (finalize h)

/-- `txid_inner` (lines 682–707). -/
def txidInner (p : Parts) : Option Blake2bHash := do
  let header ← hashHeader p
  let transparent ← hashTransparentTxid p.inputs p.outputs
  let sapling ← hashSaplingTxid p.sapling p.version
  let orchard ← hashBundleTxid p.orchard p.version.orchardFormat
  let ironwood ← if p.version.hasIronwood then some <$> hashBundleTxid p.ironwood .ironwoodV6
    else pure none
  combineTxidDigests p.consensusBranchId header transparent sapling orchard ironwood

/-- `hash_transparent_auth` (lines 715–738): `coinbase_script`'s `expect` panics on a coinbase
    input whose `scriptSig` it cannot rebuild. -/
def hashTransparentAuth (cs : CoinbaseScript) (inputs : List Input) (outputs : List Output) :
    Option Blake2bHash := do
  if inputs.isEmpty && outputs.isEmpty then return EMPTY_TRANSPARENT_AUTH_HASH
  let mut h ← hasher (personal "ZTxAuthTransHash")
  for input in inputs do
    match input with
    | .prevOut _ unlockScript _ => h ← updateSerialized h (serializeBytes unlockScript)
    | .coinbase .. =>
      let script ← input.coinbaseScript cs
      h ← updateSerialized h (serializeBytes script)
  pure (finalize h)

/-- `Zip244Version::sapling_auth_personalization` (lines 223–228). -/
def Version.saplingAuthPersonalization : Version → Bytes 16
  | .v5 => personal "ZTxAuthSapliHash"
  | .v6 => personal "ZTxAuthSapliH_v6"

/-- `Zip244Version::empty_sapling_auth_hash` (lines 230–235). -/
def Version.emptySaplingAuthHash : Version → Blake2bHash
  | .v5 => EMPTY_SAPLING_V5_AUTH_HASH
  | .v6 => EMPTY_SAPLING_V6_AUTH_HASH

/-- `Zip244Version::sapling_auth_includes_anchor` (lines 237–242). -/
def Version.saplingAuthIncludesAnchor : Version → Bool
  | .v5 => false
  | .v6 => true

/-- `hash_sapling_auth` (lines 744–772). -/
def hashSaplingAuth (sapling : Option SaplingData) (version : Version) : Option Blake2bHash := do
  let some sapling := sapling | return version.emptySaplingAuthHash
  let mut h ← hasher version.saplingAuthPersonalization
  for spend in sapling.spends do
    h := update h spend.zkproof.toList
  for spend in sapling.spends do
    h := update h spend.spendAuthSig.toList
  for output in sapling.outputs do
    h := update h output.zkproof.toList
  h := update h sapling.bindingSig.toList
  if version.saplingAuthIncludesAnchor && !sapling.spends.isEmpty then
    let anchor ← sapling.sharedAnchor
    h := update h anchor.toList
  pure (finalize h)

/-- `hash_bundle_auth` (lines 777–795). -/
def hashBundleAuth (bundle : Option OrchardData) (format : Format) : Option Blake2bHash := do
  let some bundle := bundle | return format.emptyAuthHash
  let mut h ← hasher format.personalizations.auth
  h := update h bundle.proof
  for action in bundle.actions.toList do
    h ← updateSerialized h (.ok action.spendAuthSig.toList)
  h ← updateSerialized h (.ok bundle.bindingSig.toList)
  if format.includesAnchorInAuthorizingDigest then
    h := update h bundle.sharedAnchor.toList
  pure (finalize h)

/-- `auth_digest_inner` (lines 801–831). -/
def authDigestInner (cs : CoinbaseScript) (p : Parts) : Option Blake2bHash := do
  let transparent ← hashTransparentAuth cs p.inputs p.outputs
  let sapling ← hashSaplingAuth p.sapling p.version
  let orchard ← hashBundleAuth p.orchard p.version.orchardFormat
  let ironwood ← if p.version.hasIronwood then some <$> hashBundleAuth p.ironwood .ironwoodV6
    else pure none
  let mut h ← hasher (branchPersonalization (Spec.ascii "ZTxAuthHash_" 12) p.consensusBranchId)
  h := update h transparent
  h := update h sapling
  h := update h orchard
  if let some ironwood := ironwood then
    h := update h ironwood
  pure (finalize h)

/-! ## The signature digest cache (lines 837–1011) -/

/-- `CanonicalHashType` (`src/transaction/sighash.rs`, lines 42–55). -/
inductive CanonicalHashType where
  | all
  | none
  | single
  | allAnyoneCanPay
  | noneAnyoneCanPay
  | singleAnyoneCanPay
  deriving DecidableEq

/-- `CanonicalHashType::encode` (lines 58–60), through `SighashType`'s constants. -/
def CanonicalHashType.encode : CanonicalHashType → Byte
  | .all => 0x01
  | .none => 0x02
  | .single => 0x03
  | .allAnyoneCanPay => 0x81
  | .noneAnyoneCanPay => 0x82
  | .singleAnyoneCanPay => 0x83

/-- `CanonicalHashType::anyone_can_pay` (lines 62–67). -/
def CanonicalHashType.anyoneCanPay : CanonicalHashType → Bool
  | .allAnyoneCanPay | .noneAnyoneCanPay | .singleAnyoneCanPay => true
  | _ => false

/-- `CanonicalHashType::is_single` (lines 69–71). -/
def CanonicalHashType.isSingle : CanonicalHashType → Bool
  | .single | .singleAnyoneCanPay => true
  | _ => false

/-- `CanonicalHashType::is_none` (lines 73–75). -/
def CanonicalHashType.isNone : CanonicalHashType → Bool
  | .none | .noneAnyoneCanPay => true
  | _ => false

/-- `Zip244SighashCache` (lines 837–854). -/
structure Zip244SighashCache where
  consensusBranchId : BitVec 32
  header : Blake2bHash
  transparentTxid : Blake2bHash
  prevouts : Blake2bHash
  amounts : Blake2bHash
  scriptpubkeys : Blake2bHash
  sequence : Blake2bHash
  outputs : Blake2bHash
  transparentOutputCount : ℕ
  singleOutputs : List Blake2bHash
  txins : List (Option Blake2bHash)
  transparentBundlePresent : Bool
  transparentIsCoinbaseOrHasNoInputs : Bool
  sapling : Blake2bHash
  orchard : Blake2bHash
  ironwood : Option Blake2bHash

/-- `Transaction::is_coinbase` (`src/transaction.rs`, lines 758–764). -/
def isCoinbase (inputs : List Input) : Bool :=
  match inputs with
  | [.coinbase ..] => true
  | _ => false

/-- `Zip244SighashCache::new` (lines 861–908), for the transaction's parts. The `txins` entry
    of an input is computed with its previous output, if there is one. -/
def Zip244SighashCache.new (p : Parts) (previousOutputs : List Output) :
    Option Zip244SighashCache := do
  let prevouts ← hashPrevouts p.inputs
  let sequence ← hashSequence p.inputs
  let outputs ← hashOutputs p.outputs
  let transparentBundlePresent := !p.inputs.isEmpty || !p.outputs.isEmpty
  let txins ← (p.inputs.zipIdx.mapM fun (input, index) =>
    match previousOutputs[index]? with
    | some previousOutput => hashTxin input previousOutput
    | none => pure none)
  pure
    { consensusBranchId := p.consensusBranchId
      header := ← hashHeader p
      transparentTxid := ← hashTransparentTxidFromDigests transparentBundlePresent prevouts
        sequence outputs
      prevouts
      amounts := ← hashAmounts previousOutputs
      scriptpubkeys := ← hashScriptpubkeys previousOutputs
      sequence
      outputs
      transparentOutputCount := p.outputs.length
      singleOutputs := ← (p.outputs.take p.inputs.length).mapM fun output => hashOutputs [output]
      txins
      transparentBundlePresent
      transparentIsCoinbaseOrHasNoInputs := isCoinbase p.inputs || p.inputs.isEmpty
      sapling := ← hashSaplingTxid p.sapling p.version
      orchard := ← hashBundleTxid p.orchard p.version.orchardFormat
      ironwood := ← if p.version.hasIronwood then some <$> hashBundleTxid p.ironwood .ironwoodV6
        else pure none }

/-- `Zip244SighashCache::has_corresponding_output` (lines 937–939). -/
def Zip244SighashCache.hasCorrespondingOutput (self : Zip244SighashCache) (inputIndex : ℕ) :
    Bool :=
  inputIndex < self.transparentOutputCount

/-- `Zip244SighashCache::transparent_sig_digest` (lines 941–1006): the `expect`s panic for a
    `SIGHASH_SINGLE` input without a corresponding output, and for an input without a matching
    previous output. -/
def Zip244SighashCache.transparentSigDigest (self : Zip244SighashCache)
    (hashType : CanonicalHashType) (inputIndex : Option ℕ) : Option Blake2bHash := do
  if !self.transparentBundlePresent || self.transparentIsCoinbaseOrHasNoInputs then
    return self.transparentTxid
  let hashType := if inputIndex.isNone then CanonicalHashType.all else hashType
  let anyoneCanPay := hashType.anyoneCanPay
  let single := hashType.isSingle
  -- The Rust's `none`.
  let isNone := hashType.isNone
  let prevouts ← if anyoneCanPay then hashPrevouts [] else pure self.prevouts
  let amounts ← if anyoneCanPay then hashAmounts [] else pure self.amounts
  let scriptpubkeys ← if anyoneCanPay then hashScriptpubkeys [] else pure self.scriptpubkeys
  let sequence ← if anyoneCanPay then hashSequence [] else pure self.sequence
  let outputs ← match inputIndex with
    | some index =>
      (if single then self.singleOutputs[index]?
        else if isNone then hashOutputs [] else pure self.outputs)
    | none => pure self.outputs
  let txin ← match inputIndex with
    | some index => (self.txins[index]?).join
    | none => do pure (finalize (← hasher (personal "Zcash___TxInHash")))
  let mut h ← hasher (personal "ZTxIdTranspaHash")
  h := update h [hashType.encode]
  h := update h prevouts
  h := update h amounts
  h := update h scriptpubkeys
  h := update h sequence
  h := update h outputs
  h := update h txin
  pure (finalize h)

/-- `Zip244SighashCache::sighash` (lines 915–934). -/
def Zip244SighashCache.sighash (self : Zip244SighashCache) (hashType : CanonicalHashType)
    (inputIndex : Option ℕ) : Option Blake2bHash := do
  let transparent ← self.transparentSigDigest hashType inputIndex
  combineTxidDigests self.consensusBranchId self.header transparent self.sapling self.orchard
    self.ironwood

/-! ## `src/transaction/sighash.rs` -/

/-- `CanonicalHashType::try_from(HashType)` (lines 123–129), through
    `SighashType::try_from(HashType)` (lines 107–121) and
    `CanonicalHashType::try_from(SighashType)` (lines 91–105): the six defined hash types, an
    error for any other value. -/
def CanonicalHashType.tryFrom (hashType : Script.ZHashType) : Option CanonicalHashType :=
  if hashType = Script.ALL then some .all
  else if hashType = Script.NONE then some .none
  else if hashType = Script.SINGLE then some .single
  else if hashType = Script.ALL_ANYONECANPAY then some .allAnyoneCanPay
  else if hashType = Script.NONE_ANYONECANPAY then some .noneAnyoneCanPay
  else if hashType = Script.SINGLE_ANYONECANPAY then some .singleAnyoneCanPay
  else none

/-- `SigHasher::sighash` (lines 206–228) for a version 5 or 6 transaction, whose `zip244` cache
    is `cache`: the `expect` and the `assert!` panic for a hash type that is not canonical, and
    for `SIGHASH_SINGLE` without a corresponding output. -/
def sigHasherSighash (cache : Zip244SighashCache) (hashType : Script.ZHashType)
    (inputIndexScriptCode : Option (ℕ × List Byte)) : Option Blake2bHash := do
  let canonicalHashType ← CanonicalHashType.tryFrom hashType
  if let some (inputIndex, _) := inputIndexScriptCode then
    guard (!canonicalHashType.isSingle || cache.hasCorrespondingOutput inputIndex)
  cache.sighash canonicalHashType (inputIndexScriptCode.map (·.1))

/-- `txid` (lines 1013–1015). -/
def txid (p : Parts) : Option Blake2bHash := txidInner p

/-- `auth_digest` (lines 1019–1021). -/
def authDigest (cs : CoinbaseScript) (p : Parts) : Option Blake2bHash := authDigestInner cs p

end ZcashSighash.Verifier.Native
