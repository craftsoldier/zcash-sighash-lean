/-
`zcash_primitives` 0.31.0's `Transaction::write` (`src/transaction/mod.rs`,
`src/transaction/components/{sapling,orchard}.rs`), and the writers it calls in
`zcash_transparent` 0.11.0 (`Verifier/Transparent.lean`), under the default features (no
`zip-233`), into a `Vec<u8>`.

An Orchard-shaped bundle's `BundleVersion` is not held (`Verifier/Shielded.lean`). The version
`write_v6_bundle` checks is computed here from the transaction's consensus branch ID and the
bundle's pool, as `bundle_version_for_branch`: the version `read_v6_bundle` gives a bundle it
reads. So the writer is the crate's for a transaction `Transaction::read` returned; a bundle built
otherwise may hold another version.
-/
module

public import ZcashSighash.Verifier.SighashV4

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes)

/-! ## `zcash_protocol` 0.11.0, `src/consensus.rs` -/

/-- `OrchardProtocolRevision` (lines 1085–1099). -/
inductive OrchardProtocolRevision where
  | insecureV1
  | v2
  | v3

/-- `BranchId` (lines 858–888), without `NuTachyon`, which only `zcash_unstable = "nutachyon"`
    has. -/
inductive BranchId where
  | sprout
  | overwinter
  | sapling
  | blossom
  | heartwood
  | canopy
  | nu5
  | nu6
  | nu6_1
  | nu6_2
  | nu6_3
  | nu7

/-- `BranchId::try_from` (lines 893–915): an error for an unknown branch ID. -/
def BranchId.tryFrom (value : BitVec 32) : Option BranchId :=
  if value = 0 then some .sprout
  else if value = 0x5ba81b19 then some .overwinter
  else if value = 0x76b809bb then some .sapling
  else if value = 0x2bb40e60 then some .blossom
  else if value = 0xf5b9230b then some .heartwood
  else if value = 0xe9ff75a6 then some .canopy
  else if value = 0xc2d6d0b4 then some .nu5
  else if value = 0xc8e71055 then some .nu6
  else if value = 0x4dec4df0 then some .nu6_1
  else if value = 0x5437f330 then some .nu6_2
  else if value = 0x37a5165b then some .nu6_3
  else if value = 0x77190ad9 then some .nu7
  else none

/-- `BranchId::orchard_protocol_revision` (lines 1064–1075): none before NU5. -/
def BranchId.orchardProtocolRevision : BranchId → Option OrchardProtocolRevision
  | .sprout | .overwinter | .sapling | .blossom | .heartwood | .canopy => none
  | .nu5 | .nu6 | .nu6_1 => some .insecureV1
  | .nu6_2 => some .v2
  | .nu6_3 | .nu7 => some .v3

/-- The Orchard protocol revision of a transaction's consensus branch ID: `Transaction::read`
    holds it as the `BranchId` `try_from` gives (`read_header_fragment`,
    `src/transaction/mod.rs`, lines 1152–1170), here none for an unknown one. -/
def orchardProtocolRevision (branchId : BitVec 32) : Option OrchardProtocolRevision :=
  (BranchId.tryFrom branchId).bind BranchId.orchardProtocolRevision

/-! ## `zcash_primitives` 0.31.0, `src/transaction/components/orchard.rs` -/

/-- `BundleVersion` (`orchard` 0.16.0, `src/bundle.rs`, lines 73–76): the four its constructors
    build (lines 81–113), a value pool and a protocol version. -/
inductive Orchard.BundleVersion where
  | orchardInsecureV1
  | orchardV2
  | orchardV3
  | ironwoodV3

/-- `bundle_version_for_branch` (lines 169–185). -/
def bundleVersionForBranch (consensusBranchId : BitVec 32) (pool : Orchard.ValuePool) :
    Option Orchard.BundleVersion := do
  let revision ← orchardProtocolRevision consensusBranchId
  match pool with
  | .orchard => some (match revision with
    | .insecureV1 => .orchardInsecureV1
    | .v2 => .orchardV2
    | .v3 => .orchardV3)
  | .ironwood => match revision with
    | .insecureV1 | .v2 => none
    | .v3 => some .ironwoodV3

/-- `check_v6_bundle_version` (lines 209–220). -/
def checkV6BundleVersion (bundleVersion : Orchard.BundleVersion) : IoResult Unit :=
  match bundleVersion with
  | .orchardV3 | .ironwoodV3 => .ok ()
  | _ => .error ()

/-- `write_action_without_auth` (lines 416–426), through `write_value_commitment`,
    `write_nullifier`, `write_verification_key`, `write_cmx` and `write_note_ciphertext` (lines
    388–414). -/
def writeActionWithoutAuth {W : Type} [Write W] (writer : W) (act : Orchard.Action) :
    IoResult W := do
  let writer ← Write.writeAll writer act.cvNet.toList
  let writer ← Write.writeAll writer act.nf.toList
  let writer ← Write.writeAll writer act.rk.toList
  let writer ← Write.writeAll writer act.cmx.toList
  let writer ← Write.writeAll writer act.epkBytes.toList
  let writer ← Write.writeAll writer act.encCiphertext.toList
  Write.writeAll writer act.outCiphertext.toList

/-- `write_bundle` (lines 330–362), with `Vector::write_nonempty` (`zcash_encoding` 0.5.0,
    `src/lib.rs`, lines 208–218). -/
def writeOrchardBundle {W : Type} [Write W] (bundle : Option Orchard.Bundle) (writer : W) :
    IoResult W :=
  match bundle with
  | some bundle => do
    let writer ← CompactSize.write writer bundle.actions.toList.length
    let writer ← bundle.actions.toList.foldlM writeActionWithoutAuth writer
    let writer ← Write.writeAll writer [bundle.flagByte]
    let writer ← Write.writeAll writer (toLeBytes 8 bundle.valueBalance)
    let writer ← Write.writeAll writer bundle.anchor.toList
    let writer ← Vector.write writer bundle.proof fun w b => Write.writeAll w [b]
    let writer ← Array.write writer (bundle.actions.toList.map (·.authorization))
      fun w auth => Write.writeAll w auth.toList
    Write.writeAll writer bundle.bindingSignature.toList
  | none => CompactSize.write writer 0

/-- `write_v6_bundle` (lines 378–386), the bundle's version that of its pool under
    `consensusBranchId`. No version (a pool the branch does not support) is an error, as
    `read_v6_bundle` gives such a bundle none. -/
def writeV6OrchardBundle {W : Type} [Write W] (consensusBranchId : BitVec 32)
    (bundle : Option Orchard.Bundle) (writer : W) : IoResult W := do
  if let some bundle := bundle then
    match bundleVersionForBranch consensusBranchId bundle.valuePool with
    | some bundleVersion => checkV6BundleVersion bundleVersion
    | none => .error ()
  writeOrchardBundle bundle writer

/-! ## `zcash_primitives` 0.31.0, `src/transaction/components/sapling.rs` -/

/-- `write_spend_v4` (lines 247–254). -/
def writeSpendV4 {W : Type} [Write W] (writer : W) (spend : Sapling.SpendDescription) :
    IoResult W := do
  let writer ← Write.writeAll writer spend.cv.toList
  let writer ← Write.writeAll writer spend.anchor.toList
  let writer ← Write.writeAll writer spend.nullifier.toList
  let writer ← Write.writeAll writer spend.rk.toList
  let writer ← Write.writeAll writer spend.zkproof.toList
  Write.writeAll writer spend.spendAuthSig.toList

/-- `write_spend_v5_without_witness_data` (lines 256–263). -/
def writeSpendV5WithoutWitnessData {W : Type} [Write W] (writer : W)
    (spend : Sapling.SpendDescription) : IoResult W := do
  let writer ← Write.writeAll writer spend.cv.toList
  let writer ← Write.writeAll writer spend.nullifier.toList
  Write.writeAll writer spend.rk.toList

/-- `write_output_v5_without_proof` (lines 333–342). -/
def writeOutputV5WithoutProof {W : Type} [Write W] (writer : W)
    (output : Sapling.OutputDescription) : IoResult W := do
  let writer ← Write.writeAll writer output.cv.toList
  let writer ← Write.writeAll writer output.cmu.toList
  let writer ← Write.writeAll writer output.ephemeralKey.toList
  let writer ← Write.writeAll writer output.encCiphertext.toList
  Write.writeAll writer output.outCiphertext.toList

/-- `write_v4_components` (lines 417–446). -/
def writeV4Components {W : Type} [Write W] (writer : W) (bundle : Option Sapling.Bundle)
    (txHasSapling : Bool) : IoResult W := do
  if txHasSapling then
    let writer ← Write.writeAll writer (toLeBytes 8 ((bundle.map (·.valueBalance)).getD 0))
    let writer ← Vector.write writer ((bundle.map (·.shieldedSpends)).getD []) writeSpendV4
    Vector.write writer ((bundle.map (·.shieldedOutputs)).getD []) writeOutputV4
  else if bundle.isSome then .error ()
  else pure writer

/-- `write_v5_bundle` (lines 507–553). -/
def writeSaplingV5 {W : Type} [Write W] (writer : W) (saplingBundle : Option Sapling.Bundle) :
    IoResult W :=
  match saplingBundle with
  | some bundle => do
    let writer ← Vector.write writer bundle.shieldedSpends writeSpendV5WithoutWitnessData
    let writer ← Vector.write writer bundle.shieldedOutputs writeOutputV5WithoutProof
    let writer ← if !(bundle.shieldedSpends.isEmpty && bundle.shieldedOutputs.isEmpty) then
        Write.writeAll writer (toLeBytes 8 bundle.valueBalance)
      else pure writer
    let writer ← match bundle.shieldedSpends with
      | spend :: _ => Write.writeAll writer spend.anchor.toList
      | [] => pure writer
    let writer ← Array.write writer (bundle.shieldedSpends.map (·.zkproof))
      fun w e => Write.writeAll w e.toList
    let writer ← Array.write writer (bundle.shieldedSpends.map (·.spendAuthSig))
      fun w e => Write.writeAll w e.toList
    let writer ← Array.write writer (bundle.shieldedOutputs.map (·.zkproof))
      fun w e => Write.writeAll w e.toList
    if !(bundle.shieldedSpends.isEmpty && bundle.shieldedOutputs.isEmpty) then
      Write.writeAll writer bundle.bindingSig.toList
    else pure writer
  | none => do
    let writer ← CompactSize.write writer 0
    CompactSize.write writer 0

/-! ## `zcash_primitives` 0.31.0, `src/transaction/mod.rs` -/

/-- `write_transparent` (lines 1243–1253). -/
def TransactionData.writeTransparent {W : Type} [Write W] (self : TransactionData)
    (writer : W) : IoResult W :=
  match self.transparentBundle with
  | some bundle => do
    let writer ← Vector.write writer bundle.vin fun w e => e.write w
    Vector.write writer bundle.vout fun w e => e.write w
  | none => do
    let writer ← CompactSize.write writer 0
    CompactSize.write writer 0

/-- `write_v4` (lines 1202–1241). `TxVersion::write` (lines 148–154) writes the bytes
    `TxVersion.write` gives. -/
def TransactionData.writeV4 {W : Type} [Write W] (self : TransactionData) (writer : W) :
    IoResult W := do
  if self.orchardBundle.isSome then .error ()
  let writer ← Write.writeAll writer self.version.write
  let writer ← self.writeTransparent writer
  let writer ← Write.writeAll writer (toLeBytes 4 self.lockTime)
  let writer ← if self.version.hasOverwinter then
      Write.writeAll writer (toLeBytes 4 self.expiryHeight)
    else pure writer
  let writer ← writeV4Components writer self.saplingBundle self.version.hasSapling
  let writer ← if self.version.hasSprout then
      match self.sproutBundle with
      | some bundle => do
        let writer ← Vector.write writer bundle.joinsplits fun w e => e.write w
        let writer ← Write.writeAll writer bundle.joinsplitPubkey.toList
        Write.writeAll writer bundle.joinsplitSig.toList
      | none => CompactSize.write writer 0
    else pure writer
  match self.version.hasSapling, self.saplingBundle with
  | true, some bundle => Write.writeAll writer bundle.bindingSig.toList
  | _, _ => pure writer

/-- `write_v5_header` (lines 1287–1293), and `write_v6_header` (lines 1295–1302), the same
    without `zip-233`. -/
def TransactionData.writeV5Header {W : Type} [Write W] (self : TransactionData) (writer : W) :
    IoResult W := do
  let writer ← Write.writeAll writer self.version.write
  let writer ← Write.writeAll writer (toLeBytes 4 self.consensusBranchId)
  let writer ← Write.writeAll writer (toLeBytes 4 self.lockTime)
  Write.writeAll writer (toLeBytes 4 self.expiryHeight)

/-- `write_v5` (lines 1255–1268), with `write_v5_sapling` (lines 1312–1314) and
    `write_v5_bundle` (`components/orchard.rs`, lines 368–373). -/
def TransactionData.writeV5 {W : Type} [Write W] (self : TransactionData) (writer : W) :
    IoResult W := do
  if self.sproutBundle.isSome then .error ()
  let writer ← self.writeV5Header writer
  let writer ← self.writeTransparent writer
  let writer ← writeSaplingV5 writer self.saplingBundle
  writeOrchardBundle self.orchardBundle writer

/-- `write_v6` (lines 1270–1285). -/
def TransactionData.writeV6 {W : Type} [Write W] (self : TransactionData) (writer : W) :
    IoResult W := do
  if self.sproutBundle.isSome then .error ()
  let writer ← self.writeV5Header writer
  let writer ← self.writeTransparent writer
  let writer ← writeSaplingV5 writer self.saplingBundle
  let writer ← writeV6OrchardBundle self.consensusBranchId self.orchardBundle writer
  writeV6OrchardBundle self.consensusBranchId self.ironwoodBundle writer

/-- `Transaction::write` (lines 1192–1200). -/
def TransactionData.write {W : Type} [Write W] (self : TransactionData) (writer : W) :
    IoResult W :=
  match self.version with
  | .sprout _ | .v3 | .v4 => self.writeV4 writer
  | .v5 => self.writeV5 writer
  | .v6 => self.writeV6 writer

end ZcashSighash.Verifier
