/-
The Sprout bundle of `zcash_primitives` 0.31.0 (`src/transaction/components/sprout.rs`), the
Sapling bundle of `sapling-crypto` 0.9.0 (`src/bundle.rs`), the Orchard-shaped bundle of
`orchard` 0.16.0 (`src/bundle.rs`, `src/action.rs`, `src/note.rs`), and `orchard`'s digests of
it (`src/bundle/commitments.rs`).

Each field the digests read is held as the bytes they read: `to_bytes`, `to_repr`, `as_ref` or
`<[u8; n]>::from` of its type. An Orchard bundle's flags are held as `flag_byte()` (lines
585–589), which cannot panic: a `Bundle` is constructed only with flags its version can encode.
-/
module

public import ZcashSighash.Verifier.Encoding

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)

namespace Sprout

/-- `SproutProof` (`components/sprout.rs`, lines 36–39): BCTV14 (`PHGR`, 296 bytes, line 10) or
    Groth16 (192 bytes, `components.rs`, line 9). -/
inductive SproutProof where
  | groth (p : Bytes 192)
  | phgr (p : Bytes 296)

/-- `JsDescription` (lines 51–62); a `ZatBalance` is its `i64`. -/
structure JsDescription where
  vpubOld : BitVec 64
  vpubNew : BitVec 64
  anchor : Bytes 32
  nullifiers : Bytes 32 × Bytes 32
  commitments : Bytes 32 × Bytes 32
  ephemeralKey : Bytes 32
  randomSeed : Bytes 32
  macs : Bytes 32 × Bytes 32
  proof : SproutProof
  ciphertexts : Bytes 601 × Bytes 601

/-- `JsDescription::write` (lines 168–189). -/
def JsDescription.write {W : Type} [Write W] (self : JsDescription) (writer : W) :
    IoResult W := do
  let writer ← Write.writeAll writer (toLeBytes 8 self.vpubOld)
  let writer ← Write.writeAll writer (toLeBytes 8 self.vpubNew)
  let writer ← Write.writeAll writer self.anchor.toList
  let writer ← Write.writeAll writer self.nullifiers.1.toList
  let writer ← Write.writeAll writer self.nullifiers.2.toList
  let writer ← Write.writeAll writer self.commitments.1.toList
  let writer ← Write.writeAll writer self.commitments.2.toList
  let writer ← Write.writeAll writer self.ephemeralKey.toList
  let writer ← Write.writeAll writer self.randomSeed.toList
  let writer ← Write.writeAll writer self.macs.1.toList
  let writer ← Write.writeAll writer self.macs.2.toList
  let writer ← match self.proof with
    | .groth p => Write.writeAll writer p.toList
    | .phgr p => Write.writeAll writer p.toList
  let writer ← Write.writeAll writer self.ciphertexts.1.toList
  Write.writeAll writer self.ciphertexts.2.toList

/-- `Bundle` (lines 16–20). -/
structure Bundle where
  joinsplits : List JsDescription
  joinsplitPubkey : Bytes 32
  joinsplitSig : Bytes 64

end Sprout

namespace Sapling

/-- `SpendDescription` (`sapling-crypto`, `src/bundle.rs`, lines 218–225), authorized. -/
structure SpendDescription where
  cv : Bytes 32
  anchor : Bytes 32
  nullifier : Bytes 32
  rk : Bytes 32
  zkproof : Bytes 192
  spendAuthSig : Bytes 64

/-- `OutputDescription` (lines 336–343), authorized. -/
structure OutputDescription where
  cv : Bytes 32
  cmu : Bytes 32
  ephemeralKey : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  zkproof : Bytes 192

/-- `Bundle<Authorized, ZatBalance>` (lines 57–62, `Authorized` lines 45–48); a `ZatBalance` is
    its `i64`. -/
structure Bundle where
  shieldedSpends : List SpendDescription
  shieldedOutputs : List OutputDescription
  valueBalance : BitVec 64
  bindingSig : Bytes 64

end Sapling

namespace Orchard

/-- `NonEmpty` (`nonempty` 0.11): a first element and the rest. -/
structure NonEmpty (α : Type) where
  head : α
  tail : List α

/-- `NonEmpty::iter`. -/
def NonEmpty.toList {α : Type} (self : NonEmpty α) : List α := self.head :: self.tail

/-- `Action<Signature<SpendAuth>>` (`src/action.rs`, lines 25–38), with its
    `TransmittedNoteCiphertext` (`src/note.rs`, lines 446–454). -/
structure Action where
  nf : Bytes 32
  rk : Bytes 32
  cmx : Bytes 32
  epkBytes : Bytes 32
  encCiphertext : Bytes 580
  outCiphertext : Bytes 80
  cvNet : Bytes 32
  authorization : Bytes 64

/-- `ValuePool` (`src/lib.rs`, lines 168–173). -/
inductive ValuePool where
  | orchard
  | ironwood

/-- `TxVersion` (`src/bundle.rs`, lines 204–209). -/
inductive TxVersion where
  | v5
  | v6

/-- `Bundle<Authorized, ZatBalance>` (`src/bundle.rs`, lines 440–461; `Authorized` lines
    824–827), with the value pool of its `bundle_version`. -/
structure Bundle where
  actions : NonEmpty Action
  flagByte : Byte
  valueBalance : BitVec 64
  anchor : Bytes 32
  proof : List Byte
  bindingSignature : Bytes 64
  valuePool : ValuePool

/-- `CommitmentError` (`src/bundle.rs`, lines 900–906). -/
inductive CommitmentError where
  | invalidTransactionVersion

/-! ## `src/bundle/commitments.rs` -/

/-- `BundleCommitmentPersonalizations` (lines 24–30). -/
structure Personalizations where
  bundle : Bytes 16
  actionsCompact : Bytes 16
  actionsMemos : Bytes 16
  actionsNoncompact : Bytes 16
  auth : Bytes 16

/-- `ORCHARD_V5_PERSONALIZATIONS` (lines 32–39, constants lines 10–15). -/
def ORCHARD_V5_PERSONALIZATIONS : Personalizations :=
  ⟨personal "ZTxIdOrchardHash", personal "ZTxIdOrcActCHash", personal "ZTxIdOrcActMHash",
    personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaHash"⟩

/-- `ORCHARD_V6_PERSONALIZATIONS` (lines 46–53). -/
def ORCHARD_V6_PERSONALIZATIONS : Personalizations :=
  ⟨personal "ZTxIdOrchardH_v6", personal "ZTxIdOrcActCHash", personal "ZTxIdOrcActMHash",
    personal "ZTxIdOrcActNHash", personal "ZTxAuthOrchaH_v6"⟩

/-- `IRONWOOD_V6_PERSONALIZATIONS` (lines 55–62, constants lines 17–21). -/
def IRONWOOD_V6_PERSONALIZATIONS : Personalizations :=
  ⟨personal "ZTxIdIronwd_H_v6", personal "ZTxIdIrnActCH_v6", personal "ZTxIdIrnActMH_v6",
    personal "ZTxIdIrnActNH_v6", personal "ZTxAuthIrnwdH_v6"⟩

/-- `BundleCommitmentFormat` (lines 69–73). -/
inductive BundleCommitmentFormat where
  | orchardV5
  | orchardV6
  | ironwoodV6

/-- `ValuePool::commitment_format` (lines 76–86). -/
def ValuePool.commitmentFormat : ValuePool → TxVersion →
    Except CommitmentError BundleCommitmentFormat
  | .orchard, .v5 => .ok .orchardV5
  | .orchard, .v6 => .ok .orchardV6
  | .ironwood, .v5 => .error .invalidTransactionVersion
  | .ironwood, .v6 => .ok .ironwoodV6

/-- `BundleCommitmentFormat::personalizations` (lines 90–96). -/
def BundleCommitmentFormat.personalizations : BundleCommitmentFormat → Personalizations
  | .orchardV5 => ORCHARD_V5_PERSONALIZATIONS
  | .orchardV6 => ORCHARD_V6_PERSONALIZATIONS
  | .ironwoodV6 => IRONWOOD_V6_PERSONALIZATIONS

/-- `BundleCommitmentFormat::includes_anchor_in_txid_digest` (lines 98–100). -/
def BundleCommitmentFormat.includesAnchorInTxidDigest : BundleCommitmentFormat → Bool
  | .orchardV5 => true
  | _ => false

/-- `BundleCommitmentFormat::includes_anchor_in_authorizing_digest` (lines 102–107). -/
def BundleCommitmentFormat.includesAnchorInAuthorizingDigest : BundleCommitmentFormat → Bool
  | .orchardV6 | .ironwoodV6 => true
  | _ => false

/-- `hasher` (lines 110–112): `Params::new().hash_length(32).personal(personal).to_state()`. -/
def hasher (personal : Bytes 16) : Option Blake2b.State := do
  let params ← Blake2b.Params.new.hashLength? 32
  let params ← params.personal? (personal.toList.map (·.toNat))
  pure params.toState

/-- `State::update`, of bytes. -/
def update (state : Blake2b.State) (bytes : List Byte) : Blake2b.State :=
  state.update (bytes.map (·.toNat))

/-- `State::finalize`, as bytes. -/
def finalize (state : Blake2b.State) : Blake2bHash :=
  state.finalize.map (BitVec.ofNat 8)

/-- `hash_bundle_txid_data` (lines 133–170). -/
def hashBundleTxidData (bundle : Bundle) (txVersion : TxVersion) :
    Option (Except CommitmentError Blake2bHash) := do
  match bundle.valuePool.commitmentFormat txVersion with
  | .error e => pure (.error e)
  | .ok format =>
    let personalizations := format.personalizations
    let mut h ← hasher personalizations.bundle
    let mut ch ← hasher personalizations.actionsCompact
    let mut mh ← hasher personalizations.actionsMemos
    let mut nh ← hasher personalizations.actionsNoncompact
    for action in bundle.actions.toList do
      ch := update ch action.nf.toList
      ch := update ch action.cmx.toList
      ch := update ch action.epkBytes.toList
      ch := update ch (action.encCiphertext.toList.take 52)
      mh := update mh ((action.encCiphertext.toList.drop 52).take (564 - 52))
      nh := update nh action.cvNet.toList
      nh := update nh action.rk.toList
      nh := update nh (action.encCiphertext.toList.drop 564)
      nh := update nh action.outCiphertext.toList
    h := update h (finalize ch)
    h := update h (finalize mh)
    h := update h (finalize nh)
    h := update h [bundle.flagByte]
    h := update h (toLeBytes 8 bundle.valueBalance)
    if format.includesAnchorInTxidDigest then
      h := update h bundle.anchor.toList
    pure (.ok (finalize h))

/-- `hash_bundle_txid_empty` (lines 176–187). -/
def hashBundleTxidEmpty (valuePool : ValuePool) (txVersion : TxVersion) :
    Option (Except CommitmentError Blake2bHash) :=
  match valuePool.commitmentFormat txVersion with
  | .error e => pure (.error e)
  | .ok format => do pure (.ok (finalize (← hasher format.personalizations.bundle)))

/-- `hash_bundle_auth_data` (lines 194–214). -/
def hashBundleAuthData (bundle : Bundle) (txVersion : TxVersion) :
    Option (Except CommitmentError Blake2bHash) := do
  match bundle.valuePool.commitmentFormat txVersion with
  | .error e => pure (.error e)
  | .ok format =>
    let mut h ← hasher format.personalizations.auth
    h := update h bundle.proof
    for action in bundle.actions.toList do
      h := update h action.authorization.toList
    h := update h bundle.bindingSignature.toList
    if format.includesAnchorInAuthorizingDigest then
      h := update h bundle.anchor.toList
    pure (.ok (finalize h))

/-- `hash_bundle_auth_empty` (lines 220–231). -/
def hashBundleAuthEmpty (valuePool : ValuePool) (txVersion : TxVersion) :
    Option (Except CommitmentError Blake2bHash) :=
  match valuePool.commitmentFormat txVersion with
  | .error e => pure (.error e)
  | .ok format => do pure (.ok (finalize (← hasher format.personalizations.auth)))

end Orchard

end ZcashSighash.Verifier
