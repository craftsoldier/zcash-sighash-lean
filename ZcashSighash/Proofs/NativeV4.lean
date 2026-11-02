/-
Zakura's own ZIP 243 signature digest (`zakura-chain`'s `sighash/v4.rs`) computes the
specification's, and with Zakura's callback (`Proofs/Script.lean`), so does the whole signature
check of a version 4 transparent input (`calculateSighash_native_v4`).
-/
module

public import ZcashSighash.Proofs.Native
public import ZcashSighash.Verifier.NativeV4

@[expose] public section

namespace ZcashSighash.Verifier.Native.V4

open Spec (Byte Bytes personal)
open Orchard (update finalize)
open Transparent (SIGHASH_ALL SIGHASH_NONE SIGHASH_SINGLE SIGHASH_MASK SIGHASH_ANYONECANPAY)

/-! ## The specification's view of Zakura's version 4 transaction -/

/-- A JoinSplit, as the specification's. -/
def JoinSplit.toSpec (js : JoinSplit) : Spec.JoinSplit :=
  ⟨js.vpubOld, js.vpubNew, js.anchor, js.nullifiers, js.commitments, js.ephemeralKey,
    js.randomSeed, js.vmacs, js.zkproof.toList, js.encCiphertexts⟩

/-- A Sapling Spend, as the specification's. -/
def Spend.toSpec (s : Spend) : Spec.SpendV4 :=
  ⟨s.cv, s.perSpendAnchor, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩

/-- A Sapling Output, as the specification's. -/
def outputToSpec (o : SaplingOutput) : Spec.SaplingOutput :=
  ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, o.zkproof⟩

/-- Zakura's version 4 transaction, as the specification's, under the branch `branchId`, each
    input spending the previous output at its index. -/
def Transaction.toSpec (branchId : BitVec 32) (previousOutputs : List Output)
    (tx : Transaction) : Spec.LegacyTransaction where
  format := .v4
  header := ⟨OVERWINTERED_FLAG ||| V4_VERSION, SAPLING_VERSION_GROUP_ID, branchId, tx.lockTime,
    tx.expiryHeight⟩
  transparent := transparentSpec tx.inputs tx.outputs previousOutputs
  joinSplits := (tx.joinsplitData.map fun d => d.joinsplits.map JoinSplit.toSpec).getD []
  joinSplitPubKey := (tx.joinsplitData.map (·.pubKey)).getD (List.Vector.replicate 32 0)
  saplingSpends := (tx.saplingShieldedData.map fun d => d.spends.map Spend.toSpec).getD []
  saplingOutputs := (tx.saplingShieldedData.map fun d => d.outputs.map outputToSpec).getD []
  valueBalance := (tx.saplingShieldedData.map (·.valueBalance)).getD 0

/-! ## The digests -/

/-- `prevouts_hash` is ZIP 143's `hashPrevouts` digest, a coinbase input's outpoint the null
    one. -/
theorem prevoutsHash_eq (inputs : List Input) :
    prevoutsHash inputs = some (blake2b256 (personal "ZcashPrevoutHash")
      (inputs.flatMap (·.prevoutSpec.encode))).toList := by
  simp only [prevoutsHash, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Input) s => update s a.prevoutSpec.encode)
    (fun a _ s => by
      cases a <;> simp [updateOutpoint, OutPoint.serialize, Input.prevoutSpec,
        Spec.OutPoint.encode, update_update, toLeBytes_u32]),
    foldl_update_absorbed]
  simp [finalize_state_absorbed]

/-- `sequence_hash` is ZIP 143's `hashSequence` digest. -/
theorem sequenceHash_eq (inputs : List Input) :
    sequenceHash inputs = some (blake2b256 (personal "ZcashSequencHash")
      (inputs.flatMap (Spec.u32 ·.sequence))).toList := by
  simp only [sequenceHash, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Input) s => update s (toLeBytes 4 a.sequence))
    (fun _ _ _ => rfl), foldl_update_absorbed]
  simp [finalize_state_absorbed, toLeBytes_u32]

/-- `output_hash` is ZIP 143's digest of one output, when its script fits in a protocol
    message. -/
theorem outputHash_eq (output : Output)
    (hk : output.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    outputHash output = some (blake2b256 (personal "ZcashOutputsHash")
      output.toSpec.encode).toList := by
  simp [outputHash, hasher_eq, updateSerialized, Output.serialize, serializeBytes_ok _ hk,
    Output.toSpec, Spec.TxOut.encode, toLeBytes_i64, bind, Except.bind, pure, Except.pure,
    update_absorbed, finalize_state_absorbed]

/-- `outputs_hash` is ZIP 143's `hashOutputs` digest, when the scripts fit in a protocol
    message. -/
theorem outputsHash_eq (outputs : List Output)
    (hk : ∀ o ∈ outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    outputsHash outputs = some (blake2b256 (personal "ZcashOutputsHash")
      (outputs.flatMap (·.toSpec.encode))).toList := by
  simp only [outputsHash, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Output) s => update s a.toSpec.encode)
    (fun a ha s => by
      simp [updateSerialized, Output.serialize, serializeBytes_ok _ (hk a ha), Output.toSpec,
        Spec.TxOut.encode, toLeBytes_i64, bind, Except.bind, pure, Except.pure]),
    foldl_update_absorbed]
  simp [finalize_state_absorbed]

/-- A JoinSplit's serialization is the specification's encoding. -/
theorem JoinSplit.serialize_eq (js : JoinSplit) : js.serialize = js.toSpec.encode := by
  simp [JoinSplit.serialize, JoinSplit.toSpec, Spec.JoinSplit.encode, toLeBytes_i64]

/-- `joinsplits_hash` is ZIP 143's `hashJoinSplits` digest, for JoinSplit data that has a
    JoinSplit, as its type does. -/
theorem joinsplitsHash_eq (d : Option JoinSplitData) :
    joinsplitsHash d = some (d.map fun d => (blake2b256 (personal "ZcashJSplitsHash")
      ((d.joinsplits.map JoinSplit.toSpec).flatMap Spec.JoinSplit.encode ++
        d.pubKey.toList)).toList) := by
  cases d with
  | none => rfl
  | some d =>
    simp only [joinsplitsHash, hasher_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some]
    rw [forIn_yield _ _ _ (fun (a : JoinSplit) s => update s a.toSpec.encode)
      (fun a _ s => by simp [JoinSplit.serialize_eq]), foldl_update_absorbed]
    simp [update_absorbed, finalize_state_absorbed, List.flatMap_map]

/-- `sapling_spends_hash` is ZIP 243's `hashShieldedSpends` digest, or none without Spends. -/
theorem saplingSpendsHash_eq (d : SaplingData) :
    saplingSpendsHash d = some (if d.spends.isEmpty then none
      else some (blake2b256 (personal "ZcashSSpendsHash")
        ((d.spends.map Spend.toSpec).flatMap Spec.SpendV4.encode)).toList) := by
  by_cases he : d.spends.isEmpty
  · simp [saplingSpendsHash, he]
  · simp only [saplingSpendsHash, he, hasher_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Bool.false_eq_true, ite_false]
    rw [forIn_yield _ _ _ (fun (a : Spend) s => update s a.toSpec.encode)
      (fun a _ s => by
        simp [Spend.toSpec, Spec.SpendV4.encode, update_update, List.append_assoc]),
      foldl_update_absorbed]
    simp [finalize_state_absorbed, List.flatMap_map]

/-- `sapling_outputs_hash` is ZIP 243's `hashShieldedOutputs` digest, or none without
    Outputs. -/
theorem saplingOutputsHash_eq (d : SaplingData) :
    saplingOutputsHash d = some (if d.outputs.isEmpty then none
      else some (blake2b256 (personal "ZcashSOutputHash")
        ((d.outputs.map outputToSpec).flatMap Spec.SaplingOutput.encode)).toList) := by
  by_cases he : d.outputs.isEmpty
  · simp [saplingOutputsHash, he]
  · simp only [saplingOutputsHash, he, hasher_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Bool.false_eq_true, ite_false]
    rw [forIn_yield _ _ _ (fun (a : SaplingOutput) s => update s (outputToSpec a).encode)
      (fun a _ s => by simp [SaplingOutput.serializeV4, outputToSpec, Spec.SaplingOutput.encode]),
      foldl_update_absorbed]
    simp [finalize_state_absorbed, List.flatMap_map]

/-! ## The signature digest -/

/-- The version 4 data of the specification's digests. -/
def specV4 (branchId : BitVec 32) (previousOutputs : List Output) (tx : Transaction) :
    V4Sighash where
  consensusBranchId := branchId
  lockTime := tx.lockTime
  expiryHeight := tx.expiryHeight
  inputs := tx.inputs.map fun input => ⟨input.outpoint, input.sequence⟩
  previousOutputValues := previousOutputs.map (·.value)
  prevouts := (blake2b256 (personal "ZcashPrevoutHash")
    (tx.inputs.flatMap (·.prevoutSpec.encode))).toList
  sequence := (blake2b256 (personal "ZcashSequencHash")
    (tx.inputs.flatMap (Spec.u32 ·.sequence))).toList
  outputs := (blake2b256 (personal "ZcashOutputsHash")
    (tx.outputs.flatMap (·.toSpec.encode))).toList
  singleOutputs := (tx.outputs.take tx.inputs.length).map fun o =>
    (blake2b256 (personal "ZcashOutputsHash") o.toSpec.encode).toList
  joinsplits := tx.joinsplitData.map fun d => (blake2b256 (personal "ZcashJSplitsHash")
    ((d.joinsplits.map JoinSplit.toSpec).flatMap Spec.JoinSplit.encode ++
      d.pubKey.toList)).toList
  valueBalance := (tx.saplingShieldedData.map (·.valueBalance)).getD 0
  saplingSpends := tx.saplingShieldedData.bind fun d => if d.spends.isEmpty then none
    else some (blake2b256 (personal "ZcashSSpendsHash")
      ((d.spends.map Spend.toSpec).flatMap Spec.SpendV4.encode)).toList
  saplingOutputs := tx.saplingShieldedData.bind fun d => if d.outputs.isEmpty then none
    else some (blake2b256 (personal "ZcashSOutputHash")
      ((d.outputs.map outputToSpec).flatMap Spec.SaplingOutput.encode)).toList

/-- `V4Sighash::new` computes each digest the signature digests reuse, as the specification's,
    when the output scripts fit in a protocol message. -/
theorem new_eq (branchId : BitVec 32) (previousOutputs : List Output) (tx : Transaction)
    (hk : ∀ o ∈ tx.outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    V4Sighash.new tx (some branchId) previousOutputs =
      some (some (specV4 branchId previousOutputs tx)) := by
  have hsingle : (tx.outputs.take tx.inputs.length).mapM outputHash =
      some ((tx.outputs.take tx.inputs.length).map fun o =>
        (blake2b256 (personal "ZcashOutputsHash") o.toSpec.encode).toList) :=
    mapM_some _ _ _ fun o ho => outputHash_eq o (hk o (List.mem_of_mem_take ho))
  cases hs : tx.saplingShieldedData <;>
    simp [V4Sighash.new, specV4, hs, prevoutsHash_eq, sequenceHash_eq, outputsHash_eq _ hk,
      hsingle, joinsplitsHash_eq, saplingSpendsHash_eq, saplingOutputsHash_eq]

/-- The JoinSplit, Spend and Output digests as ZIP 143 and ZIP 243 write them: the digest, or
    32 zero bytes without any. -/
theorem shielded_digests (branchId : BitVec 32) (previousOutputs : List Output)
    (tx : Transaction) :
    let s := specV4 branchId previousOutputs tx
    let t := tx.toSpec branchId previousOutputs
    s.joinsplits.getD ZERO_DIGEST = Spec.digestOrZero (!t.joinSplits.isEmpty)
        (blake2b256 (personal "ZcashJSplitsHash")
          (t.joinSplits.flatMap Spec.JoinSplit.encode ++ t.joinSplitPubKey.toList)) ∧
      s.saplingSpends.getD ZERO_DIGEST = Spec.digestOrZero (!t.saplingSpends.isEmpty)
        (blake2b256 (personal "ZcashSSpendsHash") (t.saplingSpends.flatMap Spec.SpendV4.encode)) ∧
      s.saplingOutputs.getD ZERO_DIGEST = Spec.digestOrZero (!t.saplingOutputs.isEmpty)
        (blake2b256 (personal "ZcashSOutputHash")
          (t.saplingOutputs.flatMap Spec.SaplingOutput.encode)) := by
  refine ⟨?_, ?_, ?_⟩
  · cases h : tx.joinsplitData <;>
      simp [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST, JoinSplitData.joinsplits,
        h]
  · cases h : tx.saplingShieldedData with
    | none => simp [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST, h]
    | some d => by_cases he : d.spends.isEmpty <;>
        simp_all [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST]
  · cases h : tx.saplingShieldedData with
    | none => simp [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST, h]
    | some d => by_cases he : d.outputs.isEmpty <;>
        simp_all [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST]

/-- `"ZcashSigHash" || CONSENSUS_BRANCH_ID`, as the specification writes it. -/
theorem sigHashPersonalization_eq (b : BitVec 32) :
    branchPersonalization (Spec.ascii "ZcashSigHash" 12) b =
      ⟨(Spec.ascii "ZcashSigHash" 12).toList ++ Spec.u32 b, by simp [Spec.ascii, Spec.u32,
        Spec.I2LEOSP]⟩ := rfl

/-- `signature_hash` of an input with an input tail and a previous output value hashes one
    preimage: the Rust's `update`s in order. -/
theorem signatureHash_some (s : V4Sighash) (b : Byte) (index : ℕ) (scriptCode : List Byte)
    (it : InputTail) (v : BitVec 64) (hi : s.inputs[index]? = some it)
    (hv : s.previousOutputValues[index]? = some v)
    (hsc : scriptCode.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    s.signatureHash b (some (index, scriptCode)) = some (some (blake2b256
      (branchPersonalization (Spec.ascii "ZcashSigHash" 12) s.consensusBranchId)
      (toLeBytes 4 (OVERWINTERED_FLAG ||| V4_VERSION) ++ toLeBytes 4 SAPLING_VERSION_GROUP_ID ++
        (if b &&& SIGHASH_ANYONECANPAY == 0 then s.prevouts else ZERO_DIGEST) ++
        (if b &&& SIGHASH_ANYONECANPAY == 0 && b &&& SIGHASH_MASK != SIGHASH_SINGLE &&
            b &&& SIGHASH_MASK != SIGHASH_NONE then s.sequence else ZERO_DIGEST) ++
        (if b &&& SIGHASH_MASK != SIGHASH_SINGLE && b &&& SIGHASH_MASK != SIGHASH_NONE then
            s.outputs
          else if b &&& SIGHASH_MASK == SIGHASH_SINGLE then
            (s.singleOutputs[index]?).getD ZERO_DIGEST
          else ZERO_DIGEST) ++
        s.joinsplits.getD ZERO_DIGEST ++ s.saplingSpends.getD ZERO_DIGEST ++
        s.saplingOutputs.getD ZERO_DIGEST ++ toLeBytes 4 s.lockTime ++
        toLeBytes 4 s.expiryHeight ++ toLeBytes 8 s.valueBalance ++ toLeBytes 4 (b.setWidth 32) ++
        (match it.outpoint with
          | some o => o.serialize
          | none => List.replicate 32 0 ++ toLeBytes 4 (0xffffffff : BitVec 32)) ++
        Spec.script scriptCode ++ toLeBytes 8 v ++ toLeBytes 4 it.sequence)).toList) := by
  simp only [V4Sighash.signatureHash, hi, hv, Option.isSome_some, ite_true, Option.bind_some,
    Option.pure_def, Option.bind_eq_bind, hasher_eq]
  generalize b &&& SIGHASH_ANYONECANPAY = a
  generalize b &&& SIGHASH_MASK = m
  cases it.outpoint <;> cases s.singleOutputs[index]? <;> split_ifs <;>
    simp [update_absorbed, finalize_state_absorbed, serializeBytes_ok _ hsc, updateSerialized]

/-- `signature_hash` of a transparent input is ZIP 243's digest, under any hash-type byte, when
    `scriptCode` fits in a protocol message and each input has a previous output. -/
theorem signatureHash_eq (branchId : BitVec 32) (previousOutputs : List Output)
    (tx : Transaction) (hlen : previousOutputs.length = tx.inputs.length) (b : Byte)
    (i : Fin (tx.toSpec branchId previousOutputs).transparent.vin.length)
    (scriptCode : List Byte) (hsc : scriptCode.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    (specV4 branchId previousOutputs tx).signatureHash b (some (i.val, scriptCode)) =
      some (some (Spec.legacySignatureDigest blake2b256 (tx.toSpec branchId previousOutputs)
        (.transparent b i scriptCode)).toList) := by
  obtain ⟨hj, hsp, hso⟩ := shielded_digests branchId previousOutputs tx
  have hil : i.val < tx.inputs.length := by
    simpa [Transaction.toSpec, transparentSpec] using i.isLt
  have hpl : i.val < previousOutputs.length := by omega
  have hvin : (tx.toSpec branchId previousOutputs).transparent.vin[i] =
      ⟨tx.inputs[i.val].prevoutSpec, tx.inputs[i.val].sequence,
        previousOutputs[i.val].toSpec⟩ := by
    show (transparentSpec tx.inputs tx.outputs previousOutputs).vin[i.val]'i.isLt = _
    simp [transparentSpec, List.getElem?_eq_getElem hpl]
  have hin : (specV4 branchId previousOutputs tx).inputs[i.val]? =
      some ⟨tx.inputs[i.val].outpoint, tx.inputs[i.val].sequence⟩ := by simp [specV4, hil]
  have hval : (specV4 branchId previousOutputs tx).previousOutputValues[i.val]? =
      some previousOutputs[i.val].value := by simp [specV4, hpl]
  have hsingle : (specV4 branchId previousOutputs tx).singleOutputs[i.val]? =
      (tx.outputs[i.val]?).map fun o =>
        (blake2b256 (personal "ZcashOutputsHash") o.toSpec.encode).toList := by
    simp [specV4, hil]
  rw [signatureHash_some _ b i.val scriptCode _ _ hin hval hsc, hj, hsp, hso, hsingle]
  unfold Spec.legacySignatureDigest
  simp only [hvin]
  rw [← sigHashPersonalization_eq]
  clear hj hsp hso hin hval hsingle hvin
  have hvout : (tx.toSpec branchId previousOutputs).transparent.vout[i.val]? =
      (tx.outputs[i.val]?).map Output.toSpec := by
    simp [Transaction.toSpec, transparentSpec]
  have hpre : Spec.OutPoint.encode tx.inputs[i.val].prevoutSpec =
      match tx.inputs[i.val].outpoint with
      | some o => o.serialize
      | none => List.replicate 32 0 ++ toLeBytes 4 (0xffffffff : BitVec 32) := by
    cases tx.inputs[i.val] <;>
      simp [Input.outpoint, Input.prevoutSpec, OutPoint.serialize, Spec.OutPoint.encode,
        toLeBytes_u32]
  obtain ⟨hp, hs, -, -, ho⟩ := transparentSpec_flatMaps tx.inputs tx.outputs previousOutputs hlen
  simp only [hvout, hpre, SIGHASH_ANYONECANPAY, SIGHASH_MASK, SIGHASH_SINGLE, SIGHASH_NONE,
    Spec.LegacyInput.hashType, bne, Bool.not_not]
  cases tx.outputs[i.val]? <;>
    simp [specV4, Transaction.toSpec, Spec.digestOrZero, ZERO_DIGEST, toLeBytes_u32,
      toLeBytes_i64, Output.toSpec, hp, hs, ho]

/-- `signature_hash` of a JoinSplit, Spend or binding signature is ZIP 243's digest, under
    `SIGHASH_ALL` whatever hash-type byte it is passed. -/
theorem signatureHash_shielded_eq (branchId : BitVec 32) (previousOutputs : List Output)
    (tx : Transaction) (hlen : previousOutputs.length = tx.inputs.length) (b : Byte) :
    (specV4 branchId previousOutputs tx).signatureHash b none =
      some (some (Spec.legacySignatureDigest blake2b256 (tx.toSpec branchId previousOutputs)
        .shielded).toList) := by
  obtain ⟨hj, hsp, hso⟩ := shielded_digests branchId previousOutputs tx
  obtain ⟨hp, hs, -, -, ho⟩ := transparentSpec_flatMaps tx.inputs tx.outputs previousOutputs hlen
  simp only [V4Sighash.signatureHash, Option.isSome_none, Bool.false_eq_true, ite_false,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, hasher_eq, hj, hsp, hso]
  unfold Spec.legacySignatureDigest
  rw [← sigHashPersonalization_eq]
  simp [update_absorbed, finalize_state_absorbed, specV4, Transaction.toSpec,
    Spec.LegacyInput.hashType, SIGHASH_ALL, SIGHASH_ANYONECANPAY, SIGHASH_MASK, SIGHASH_SINGLE,
    SIGHASH_NONE, Spec.digestOrZero, toLeBytes_u32, toLeBytes_i64, hp, hs, ho]

/-! ## The signature check -/

/-- **Zakura's callback gives a version 4 signature check ZIP 243's digest**, through the
    `SigHasher` its node builds: the digest of the input under the signature's own hash-type
    byte, whatever it is, and never a panic. The hypotheses are what parsing and the
    interpreter give: output scripts and the script code that fit in a protocol message, and a
    coin for each input. -/
theorem calculateSighash_native_v4 (branchId : BitVec 32) (previousOutputs : List Output)
    (tx : Transaction) (hk : ∀ o ∈ tx.outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN)
    (hlen : previousOutputs.length = tx.inputs.length) (v4 : V4Sighash)
    (hnew : V4Sighash.new tx (some branchId) previousOutputs = some (some v4))
    (sighash : Script.ZHashType → Option (ℕ × List Byte) → Option Blake2bHash)
    (version : ℕ) (hv : version < 5) (outputsLen : ℕ)
    (i : Fin (tx.toSpec branchId previousOutputs).transparent.vin.length)
    (scriptCode : List Byte) (hsc : scriptCode.length ≤ MAX_PROTOCOL_MESSAGE_LEN)
    (b : Byte) (hashType : Script.HashType)
    (hparse : Script.HashType.fromBits (b.setWidth 32) false = .ok hashType) :
    Script.calculateSighash ⟨sighash, sigHasherSighashV4Raw v4⟩ version outputsLen i.val
        scriptCode hashType =
      some (some (Spec.legacySignatureDigest blake2b256 (tx.toSpec branchId previousOutputs)
        (.transparent b i scriptCode)).toList) := by
  obtain rfl : v4 = specV4 branchId previousOutputs tx := by
    simpa [new_eq branchId previousOutputs tx hk] using hnew.symm
  exact Script.calculateSighash_v4 _ version hv outputsLen i.val scriptCode b hashType
    (Script.rawBits_of_fromBits hparse) _
    (by simp [sigHasherSighashV4Raw,
      signatureHash_eq branchId previousOutputs tx hlen b i scriptCode hsc])

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Native.V4.calculateSighash_native_v4' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms calculateSighash_native_v4

/--
info: 'ZcashSighash.Verifier.Native.V4.signatureHash_shielded_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signatureHash_shielded_eq

end ZcashSighash.Verifier.Native.V4
