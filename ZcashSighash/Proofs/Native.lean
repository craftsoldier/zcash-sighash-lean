/-
Zakura's own ZIP 244 / ZIP 229 digests (`zakura-chain`'s `zip244.rs`) compute the
specification's.

First the thirteen digests of empty components the Rust writes in as constants: each is the
BLAKE2b-256 hash of no bytes under its personalization, which the kernel checks by computing it.
-/
module

public import ZcashSighash.Proofs.Verifier
public import ZcashSighash.Verifier.Native

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes personal)
open Orchard (update finalize)

/-! ## The constants -/

/-- `EMPTY_TRANSPARENT_TXID_HASH` is §T.2's digest of no transparent component. -/
theorem EMPTY_TRANSPARENT_TXID_HASH_eq :
    EMPTY_TRANSPARENT_TXID_HASH = (blake2b256 (personal "ZTxIdTranspaHash") []).toList := by
  decide +kernel

/-- `EMPTY_SAPLING_TXID_HASH` is §T.3's digest of no Sapling component. -/
theorem EMPTY_SAPLING_TXID_HASH_eq :
    EMPTY_SAPLING_TXID_HASH = (blake2b256 (personal "ZTxIdSaplingHash") []).toList := by
  decide +kernel

/-- `EMPTY_SAPLING_SPENDS_HASH` is §T.3a's digest of no Sapling Spends. -/
theorem EMPTY_SAPLING_SPENDS_HASH_eq :
    EMPTY_SAPLING_SPENDS_HASH = (blake2b256 (personal "ZTxIdSSpendsHash") []).toList := by
  decide +kernel

/-- `EMPTY_SAPLING_OUTPUTS_HASH` is §T.3b's digest of no Sapling Outputs. -/
theorem EMPTY_SAPLING_OUTPUTS_HASH_eq :
    EMPTY_SAPLING_OUTPUTS_HASH = (blake2b256 (personal "ZTxIdSOutputHash") []).toList := by
  decide +kernel

/-- `EMPTY_ORCHARD_V5_TXID_HASH` is §T.4's digest of no Orchard Actions in version 5. -/
theorem EMPTY_ORCHARD_V5_TXID_HASH_eq :
    EMPTY_ORCHARD_V5_TXID_HASH = (blake2b256 (personal "ZTxIdOrchardHash") []).toList := by
  decide +kernel

/-- `EMPTY_ORCHARD_V6_TXID_HASH` is the digest of no Orchard Actions in version 6. -/
theorem EMPTY_ORCHARD_V6_TXID_HASH_eq :
    EMPTY_ORCHARD_V6_TXID_HASH = (blake2b256 (personal "ZTxIdOrchardH_v6") []).toList := by
  decide +kernel

/-- `EMPTY_IRONWOOD_TXID_HASH` is ZIP 229's digest of no Ironwood Actions. -/
theorem EMPTY_IRONWOOD_TXID_HASH_eq :
    EMPTY_IRONWOOD_TXID_HASH = (blake2b256 (personal "ZTxIdIronwd_H_v6") []).toList := by
  decide +kernel

/-- `EMPTY_TRANSPARENT_AUTH_HASH` is §A.1's digest of no `scriptSig`s. -/
theorem EMPTY_TRANSPARENT_AUTH_HASH_eq :
    EMPTY_TRANSPARENT_AUTH_HASH = (blake2b256 (personal "ZTxAuthTransHash") []).toList := by
  decide +kernel

/-- `EMPTY_SAPLING_V5_AUTH_HASH` is §A.2's digest of no Sapling component in version 5. -/
theorem EMPTY_SAPLING_V5_AUTH_HASH_eq :
    EMPTY_SAPLING_V5_AUTH_HASH = (blake2b256 (personal "ZTxAuthSapliHash") []).toList := by
  decide +kernel

/-- `EMPTY_SAPLING_V6_AUTH_HASH` is the digest of no Sapling component in version 6. -/
theorem EMPTY_SAPLING_V6_AUTH_HASH_eq :
    EMPTY_SAPLING_V6_AUTH_HASH = (blake2b256 (personal "ZTxAuthSapliH_v6") []).toList := by
  decide +kernel

/-- `EMPTY_ORCHARD_V5_AUTH_HASH` is §A.3's digest of no Orchard Actions in version 5. -/
theorem EMPTY_ORCHARD_V5_AUTH_HASH_eq :
    EMPTY_ORCHARD_V5_AUTH_HASH = (blake2b256 (personal "ZTxAuthOrchaHash") []).toList := by
  decide +kernel

/-- `EMPTY_ORCHARD_V6_AUTH_HASH` is the digest of no Orchard Actions in version 6. -/
theorem EMPTY_ORCHARD_V6_AUTH_HASH_eq :
    EMPTY_ORCHARD_V6_AUTH_HASH = (blake2b256 (personal "ZTxAuthOrchaH_v6") []).toList := by
  decide +kernel

/-- `EMPTY_IRONWOOD_AUTH_HASH` is ZIP 229's auth digest of no Ironwood Actions. -/
theorem EMPTY_IRONWOOD_AUTH_HASH_eq :
    EMPTY_IRONWOOD_AUTH_HASH = (blake2b256 (personal "ZTxAuthIrnwdH_v6") []).toList := by
  decide +kernel

/-! ## The specification's view of Zakura's parsed transaction -/

/-- An input's `prevout`: a coinbase input's is the null outpoint. -/
def Input.prevoutSpec : Input → Spec.OutPoint
  | .prevOut o _ _ => ⟨o.hash, o.index⟩
  | .coinbase .. => ⟨List.Vector.replicate 32 0, 0xffffffff⟩

/-- An output, as the specification's. -/
def Output.toSpec (o : Output) : Spec.TxOut := ⟨o.value, o.lockScript⟩

/-- The transparent inputs and outputs, each input spending the previous output at its index. -/
def transparentSpec (inputs : List Input) (outputs : List Output) (previousOutputs : List Output) :
    Spec.Transparent :=
  ⟨inputs.mapIdx fun i input => ⟨input.prevoutSpec, input.sequence,
      ((previousOutputs[i]?).map Output.toSpec).getD ⟨0, []⟩⟩,
    outputs.map Output.toSpec⟩

/-! ## Hashing through a `blake2b_simd` state -/

/-- `hasher p` never panics: it is the empty state personalized with `p`. -/
theorem hasher_eq (p : Bytes 16) : hasher p = some (absorbed p []).state := orchard_absorbed p

/-- `CompactSize64::zcash_serialize` is the specification's `compactSize`, below `2 ^ 64`. -/
theorem compactSize64_eq (n : ℕ) (hn : n < 2 ^ 64) :
    compactSize64 n = Spec.compactSize (BitVec.ofNat 64 n) := by
  unfold compactSize64 Spec.compactSize
  have h64 : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  rw [h64]
  split_ifs <;> first | omega |
    simp (disch := omega) [toLeBytes, Spec.I2LEOSP, List.range_succ, Nat.mod_eq_of_lt]

/-- A byte vector no longer than `MAX_PROTOCOL_MESSAGE_LEN` serializes as the specification's
    `script` field: its `compactSize` length, then its bytes. -/
theorem serializeBytes_ok (v : List Byte) (hv : v.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    serializeBytes v = .ok (Spec.script v) := by
  have h32 : ¬4294967296 ≤ v.length := by unfold MAX_PROTOCOL_MESSAGE_LEN at hv; omega
  have hmax : ¬v.length > MAX_PROTOCOL_MESSAGE_LEN := by omega
  simp [serializeBytes, h32, hmax, Spec.script,
    compactSize64_eq v.length (by unfold MAX_PROTOCOL_MESSAGE_LEN at hv; omega)]

/-! ## The transparent identifier digests -/

/-- `hash_prevouts` is §T.2a's digest, a coinbase input's outpoint the null one. -/
theorem hashPrevouts_eq (inputs : List Input) :
    hashPrevouts inputs = some (blake2b256 (personal "ZTxIdPrevoutHash")
      (inputs.flatMap (·.prevoutSpec.encode))).toList := by
  simp only [hashPrevouts, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Input) s => update s a.prevoutSpec.encode)
    (fun a _ s => by
      cases a <;> simp [updateSerialized, OutPoint.serialize, Input.prevoutSpec,
        Spec.OutPoint.encode, update_update, toLeBytes_u32]),
    foldl_update_absorbed]
  simp [finalize_state_absorbed]

/-- `hash_sequence` is §T.2b's digest. -/
theorem hashSequence_eq (inputs : List Input) :
    hashSequence inputs = some (blake2b256 (personal "ZTxIdSequencHash")
      (inputs.flatMap (Spec.u32 ·.sequence))).toList := by
  simp only [hashSequence, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Input) s => update s (toLeBytes 4 a.sequence))
    (fun _ _ _ => rfl), foldl_update_absorbed]
  simp [finalize_state_absorbed, toLeBytes_u32]

/-- `hash_outputs` is §T.2c's digest, when the scripts fit in a protocol message. -/
theorem hashOutputs_eq (outputs : List Output)
    (hk : ∀ o ∈ outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    hashOutputs outputs = some (blake2b256 (personal "ZTxIdOutputsHash")
      (outputs.flatMap (·.toSpec.encode))).toList := by
  simp only [hashOutputs, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Output) s => update s a.toSpec.encode)
    (fun a ha s => by
      simp [updateSerialized, Output.serialize, serializeBytes_ok _ (hk a ha), Output.toSpec,
        Spec.TxOut.encode, toLeBytes_i64, bind, Except.bind, pure, Except.pure]),
    foldl_update_absorbed]
  simp [finalize_state_absorbed]

/-- Flattening a `mapIdx` forgets the index when the flattened function does not use it. -/
theorem flatMap_mapIdx {α β γ : Type} (l : List α) (f : ℕ → α → β) (g : β → List γ)
    (h : α → List γ) (hg : ∀ i a, g (f i a) = h a) : (l.mapIdx f).flatMap g = l.flatMap h := by
  rw [List.flatMap_def, List.flatMap_def, map_mapIdx l f g h hg]

/-- `hash_transparent_txid` is §T.2's digest, when the output scripts fit in a protocol
    message. -/
theorem hashTransparentTxid_eq (inputs : List Input) (outputs previousOutputs : List Output)
    (hk : ∀ o ∈ outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    hashTransparentTxid inputs outputs = some (Spec.transparentDigest blake2b256
      (transparentSpec inputs outputs previousOutputs)).toList := by
  by_cases he : inputs.isEmpty && outputs.isEmpty
  · have hi : inputs = [] := by simpa using (Bool.and_eq_true_iff.mp he).1
    have ho : outputs = [] := by simpa using (Bool.and_eq_true_iff.mp he).2
    simp [hashTransparentTxid, hi, ho, Spec.transparentDigest, transparentSpec,
      EMPTY_TRANSPARENT_TXID_HASH_eq]
  · have he' : ¬((transparentSpec inputs outputs previousOutputs).vin.isEmpty &&
        (transparentSpec inputs outputs previousOutputs).vout.isEmpty) := by
      simpa [transparentSpec] using he
    have hp : (transparentSpec inputs outputs previousOutputs).vin.flatMap (·.prevout.encode) =
        inputs.flatMap (·.prevoutSpec.encode) :=
      flatMap_mapIdx _ _ _ _ fun _ _ => rfl
    have hs : (transparentSpec inputs outputs previousOutputs).vin.flatMap (Spec.u32 ·.nSequence) =
        inputs.flatMap (Spec.u32 ·.sequence) :=
      flatMap_mapIdx _ _ _ _ fun _ _ => rfl
    simp only [hashTransparentTxid, he, ite_false, Bool.false_eq_true, hashPrevouts_eq,
      hashSequence_eq, hashOutputs_eq _ hk, hashTransparentTxidFromDigests, Bool.not_true,
      hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some, update_absorbed,
      finalize_state_absorbed, Spec.transparentDigest, he', Spec.node]
    simp only [Spec.prevoutsDigest, Spec.sequenceDigest, Spec.outputsDigest, hp, hs]
    simp [transparentSpec, List.flatMap_map, Output.toSpec]

/-! ## Sapling -/

/-- A Sapling component, as the specification's: its anchor the shared one, if any. -/
def SaplingData.toSpec (s : SaplingData) : Spec.Sapling :=
  ⟨s.spends.map fun sp => ⟨sp.cv, sp.nullifier, sp.rk, sp.zkproof, sp.spendAuthSig⟩,
    s.outputs.map fun o => ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext,
      o.zkproof⟩,
    s.valueBalance, s.sharedAnchor.getD (List.Vector.replicate 32 0), s.bindingSig⟩

/-- A Sapling component has a Spend or an Output, by its type. -/
theorem SaplingData.nonempty (s : SaplingData) : s.spends ≠ [] ∨ s.outputs ≠ [] := by
  rcases s with ⟨_, _ | ⟨_, ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩⟩, _⟩ <;>
    simp [SaplingData.spends, SaplingData.outputs, Orchard.NonEmpty.toList]

/-- With a Spend, a Sapling component has its shared anchor, by its type. -/
theorem SaplingData.sharedAnchor_eq (s : SaplingData) (hs : s.spends ≠ []) :
    s.sharedAnchor = some s.toSpec.anchor := by
  rcases s with ⟨_, _ | _, _⟩ <;>
    simp_all [SaplingData.spends, SaplingData.sharedAnchor, SaplingData.toSpec]

/-- `hash_sapling_spends` is §T.3a's digest (in version 6, ZIP 229's without the anchor). The
    anchor hashed with each Spend is the shared one, as the encoding has it. -/
theorem hashSaplingSpends_eq (s : SaplingData) (v : Version) (f : Spec.Format)
    (hf : f.IsV6 = v.hasIronwood) (hs : s.spends ≠ []) :
    hashSaplingSpends s v = some (Spec.saplingSpendsDigest blake2b256 f s.toSpec).toList := by
  have hs' : s.toSpec.spends ≠ [] := by simpa [SaplingData.toSpec] using hs
  have ha := s.sharedAnchor_eq hs
  have hne : (!s.spends.isEmpty) = true := by simpa using hs
  simp only [hashSaplingSpends, hasher_eq, hne, ite_true, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Spec.saplingSpendsDigest, hs', ite_false]
  cases v
  · simp only [Version.saplingSpendsTxidIncludesAnchor, ite_true, ha, Option.map_eq_map,
      Option.map_some, Option.bind_some]
    rw [forIn_yield _ _ _ (fun (sp : SaplingSpend) st =>
      ⟨update st.1 sp.nullifier.toList,
        update st.2 (sp.cv.toList ++ s.toSpec.anchor.toList ++ sp.rk.toList)⟩)
      (fun _ _ _ => by simp [update_update])]
    rw [foldl_prod _ _ _ (fun st (sp : SaplingSpend) => update st sp.nullifier.toList)
      (fun st (sp : SaplingSpend) =>
        update st (sp.cv.toList ++ s.toSpec.anchor.toList ++ sp.rk.toList)),
      foldl_update_absorbed, foldl_update_absorbed]
    simp only [Version.hasIronwood] at hf
    simp [update_absorbed, finalize_state_absorbed, Spec.node, Spec.saplingSpendsCompactDigest,
      Spec.saplingSpendsNoncompactDigest, hf, Version.saplingSpendsNoncompactPersonalization]
    simp [SaplingData.toSpec, List.flatMap_map]
  · simp only [Version.saplingSpendsTxidIncludesAnchor, Bool.false_eq_true, ite_false]
    rw [forIn_yield _ _ _ (fun (sp : SaplingSpend) st =>
      ⟨update st.1 sp.nullifier.toList, update st.2 (sp.cv.toList ++ sp.rk.toList)⟩)
      (fun _ _ _ => by simp [update_update])]
    rw [foldl_prod _ _ _ (fun st (sp : SaplingSpend) => update st sp.nullifier.toList)
      (fun st (sp : SaplingSpend) => update st (sp.cv.toList ++ sp.rk.toList)),
      foldl_update_absorbed, foldl_update_absorbed]
    simp only [Version.hasIronwood] at hf
    simp [update_absorbed, finalize_state_absorbed, Spec.node, Spec.saplingSpendsCompactDigest,
      Spec.saplingSpendsNoncompactDigest, hf, Version.saplingSpendsNoncompactPersonalization]
    simp [SaplingData.toSpec, List.flatMap_map]

/-- `hash_sapling_outputs` is §T.3b's digest. -/
theorem hashSaplingOutputs_eq (s : SaplingData) (ho : s.outputs ≠ []) :
    hashSaplingOutputs s = some (Spec.saplingOutputsDigest blake2b256 s.toSpec).toList := by
  have ho' : s.toSpec.outputs ≠ [] := by simpa [SaplingData.toSpec] using ho
  have hne : (!s.outputs.isEmpty) = true := by simpa using ho
  simp only [hashSaplingOutputs, hasher_eq, hne, ite_true, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Spec.saplingOutputsDigest, ho', ite_false]
  rw [forIn_yield _ _ _ (fun (o : SaplingOutput) st =>
    ⟨update st.1 (o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52),
      update st.2.1 ((o.encCiphertext.toList.drop 52).take (564 - 52)),
      update st.2.2 (o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)⟩)
    (fun _ _ _ => by simp [update_update])]
  rw [foldl_prod3 _ _ _ _
    (fun st (o : SaplingOutput) =>
      update st (o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52))
    (fun st (o : SaplingOutput) => update st ((o.encCiphertext.toList.drop 52).take (564 - 52)))
    (fun st (o : SaplingOutput) =>
      update st (o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)),
    foldl_update_absorbed, foldl_update_absorbed, foldl_update_absorbed]
  simp [update_absorbed, finalize_state_absorbed, Spec.node, Spec.saplingOutputsCompactDigest,
    Spec.saplingOutputsMemosDigest, Spec.saplingOutputsNoncompactDigest, SaplingData.toSpec,
    List.flatMap_map]

/-- `hash_sapling_txid` is §T.3's Sapling digest (in version 6, ZIP 229's); no component is
    the empty one. -/
theorem hashSaplingTxid_eq (sapling : Option SaplingData) (v : Version) (f : Spec.Format)
    (hf : f.IsV6 = v.hasIronwood) :
    hashSaplingTxid sapling v = some (Spec.saplingDigest blake2b256 f
      ((sapling.map SaplingData.toSpec).getD emptySapling)).toList := by
  cases sapling with
  | none => simp [hashSaplingTxid, EMPTY_SAPLING_TXID_HASH_eq, saplingDigest_empty]
  | some s =>
    have hne : ¬(s.toSpec.spends = [] ∧ s.toSpec.outputs = []) := by
      rcases s.nonempty with h | h <;> simp [SaplingData.toSpec, h]
    by_cases hs : s.spends = [] <;> by_cases ho : s.outputs = [] <;>
      simp_all [hashSaplingTxid, hasher_eq, update_absorbed, finalize_state_absorbed,
        hashSaplingSpends_eq s v f hf, hashSaplingOutputs_eq, EMPTY_SAPLING_SPENDS_HASH_eq,
        EMPTY_SAPLING_OUTPUTS_HASH_eq, Spec.saplingDigest, Spec.saplingSpendsDigest,
        Spec.saplingOutputsDigest, toLeBytes_i64, SaplingData.toSpec]

/-! ## Orchard and Ironwood -/

/-- An Orchard-shaped component, as the specification's. -/
def OrchardData.toSpec (b : OrchardData) : Spec.OrchardBundle :=
  ⟨b.actions.toList.map fun a => ⟨a.cv, a.nullifier, a.rk, a.cmx, a.ephemeralKey,
      a.encCiphertext, a.outCiphertext, a.spendAuthSig⟩,
    b.flags, b.valueBalance, b.sharedAnchor, b.proof, b.bindingSig⟩

/-- A format's empty digest is the specification's digest of no Actions. -/
theorem emptyTxidHash_eq (format : Format) (v6 : Bool) :
    format.emptyTxidHash = (Spec.actionsDigest blake2b256 format.personalizations.toSpec v6
      emptyOrchard).toList := by
  cases format <;> simp [Format.emptyTxidHash, Spec.actionsDigest, emptyOrchard,
    Format.personalizations, Orchard.Personalizations.toSpec, EMPTY_ORCHARD_V5_TXID_HASH_eq,
    EMPTY_ORCHARD_V6_TXID_HASH_eq, EMPTY_IRONWOOD_TXID_HASH_eq]

/-- `hash_bundle_txid` is §T.4's digest under the format's personalizations, with the anchor
    exactly when the format includes it (version 5's Orchard); no component is the empty one. -/
theorem hashBundleTxid_eq (bundle : Option OrchardData) (format : Format) :
    hashBundleTxid bundle format = some (Spec.actionsDigest blake2b256
      format.personalizations.toSpec (!format.includesAnchorInTxidDigest)
      ((bundle.map OrchardData.toSpec).getD emptyOrchard)).toList := by
  cases bundle with
  | none => simpa [hashBundleTxid] using emptyTxidHash_eq format _
  | some b =>
    simp only [hashBundleTxid, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [forIn_yield _ _ _ (fun (a : Action) st =>
      ⟨update st.1 (a.nullifier.toList ++ a.cmx.toList ++ a.ephemeralKey.toList ++
          a.encCiphertext.toList.take 52),
        update st.2.1 ((a.encCiphertext.toList.drop 52).take (564 - 52)),
        update st.2.2 (a.cv.toList ++ a.rk.toList ++ a.encCiphertext.toList.drop 564 ++
          a.outCiphertext.toList)⟩)
      (fun _ _ _ => by simp [update_update])]
    rw [foldl_prod3 _ _ _ _
      (fun st (a : Action) => update st (a.nullifier.toList ++ a.cmx.toList ++
        a.ephemeralKey.toList ++ a.encCiphertext.toList.take 52))
      (fun st (a : Action) => update st ((a.encCiphertext.toList.drop 52).take (564 - 52)))
      (fun st (a : Action) => update st (a.cv.toList ++ a.rk.toList ++
        a.encCiphertext.toList.drop 564 ++ a.outCiphertext.toList)),
      foldl_update_absorbed, foldl_update_absorbed, foldl_update_absorbed]
    cases format <;>
      simp [update_absorbed, finalize_state_absorbed, Spec.actionsDigest, OrchardData.toSpec,
        Orchard.NonEmpty.toList, List.flatMap_map, toLeBytes_i64, Format.personalizations,
        Orchard.Personalizations.toSpec, Format.includesAnchorInTxidDigest]

/-! ## The transaction identifier -/

/-- `combine_txid_digests` hashes the digests in order, Ironwood's last if present. -/
theorem combineTxidDigests_eq (br : BitVec 32) (hd t s o : Blake2bHash)
    (iw : Option Blake2bHash) :
    combineTxidDigests br hd t s o iw = some (blake2b256 (Spec.txHashPersonalization br)
      (hd ++ t ++ s ++ o ++ iw.getD [])).toList := by
  cases iw <;> simp [combineTxidDigests, hasher_eq, txHashPersonalization_eq, update_absorbed,
    finalize_state_absorbed]

/-- The specification's transaction format of a version. -/
def Version.toSpec (v : Version) (ironwood : Option OrchardData) : Spec.Format :=
  match v with
  | .v5 => .v5
  | .v6 => .v6 ((ironwood.map OrchardData.toSpec).getD emptyOrchard)

/-- An input's `scriptSig`: a coinbase input's as `coinbase_script` rebuilds it. -/
def Input.scriptSig (cs : CoinbaseScript) : Input → List Byte
  | .prevOut _ s _ => s
  | input@(.coinbase ..) => (input.coinbaseScript cs).getD []

/-- Zakura's parsed transaction, as the specification's, each input spending the previous
    output at its index and a coinbase input's `scriptSig` the one `coinbase_script` rebuilds. -/
def Parts.toSpec (cs : CoinbaseScript) (previousOutputs : List Output) (p : Parts) :
    Spec.Transaction where
  format := p.version.toSpec p.ironwood
  header := ⟨p.version.header, p.version.versionGroupId, p.consensusBranchId, p.lockTime,
    p.expiryHeight⟩
  transparent := transparentSpec p.inputs p.outputs previousOutputs
  scriptSigs := p.inputs.map (·.scriptSig cs)
  sapling := (p.sapling.map SaplingData.toSpec).getD emptySapling
  orchard := (p.orchard.map OrchardData.toSpec).getD emptyOrchard

/-- `hash_header` is §T.1's digest. -/
theorem hashHeader_eq (cs : CoinbaseScript) (previousOutputs : List Output) (p : Parts) :
    hashHeader p =
      some (Spec.headerDigest blake2b256 (p.toSpec cs previousOutputs).header).toList := by
  simp [hashHeader, hasher_eq, update_absorbed, finalize_state_absorbed, Spec.headerDigest,
    Parts.toSpec, toLeBytes_u32]

/-- **Zakura's node computes the specification's transaction identifier** (ZIP 244; for version
    6, ZIP 229), for every version 5 or 6 transaction it parses whose output scripts fit in a
    protocol message, as every parsed one's do. -/
theorem txid_eq (cs : CoinbaseScript) (previousOutputs : List Output) (p : Parts)
    (hk : ∀ o ∈ p.outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN) :
    txid p = some ((p.toSpec cs previousOutputs).txid blake2b256).toList := by
  have hf : (p.version.toSpec p.ironwood).IsV6 = p.version.hasIronwood := by
    cases p.version <;> rfl
  simp only [txid, txidInner, hashHeader_eq cs previousOutputs,
    hashTransparentTxid_eq p.inputs p.outputs previousOutputs hk,
    hashSaplingTxid_eq p.sapling p.version _ hf, hashBundleTxid_eq, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some]
  rcases p with ⟨_ | _, br, lt, eh, ins, outs, sap, orc, iw⟩ <;>
    simp [combineTxidDigests_eq, Version.hasIronwood, Version.orchardFormat,
      Format.includesAnchorInTxidDigest, Format.personalizations, Orchard.Personalizations.toSpec,
      Spec.Transaction.txid, Spec.txidDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, Parts.toSpec, Version.toSpec, Spec.Format.IsV6, Spec.node,
      Spec.orchardV5, Spec.orchardV6, Spec.ironwoodV6]

/-! ## The auth digest -/

/-- What the auth digest needs of the inputs: each coinbase input's `scriptSig` can be rebuilt
    (`Input::coinbase_script`), and each `scriptSig` fits in a protocol message. -/
def Input.AuthFits (cs : CoinbaseScript) (input : Input) : Prop :=
  (∀ h d s, input = .coinbase h d s → (input.coinbaseScript cs).isSome) ∧
    (input.scriptSig cs).length ≤ MAX_PROTOCOL_MESSAGE_LEN

/-- `hash_transparent_auth` is §A.1's digest of the `scriptSig`s. -/
theorem hashTransparentAuth_eq (cs : CoinbaseScript) (inputs : List Input)
    (outputs : List Output) (hi : ∀ i ∈ inputs, i.AuthFits cs) :
    hashTransparentAuth cs inputs outputs = some (Spec.transparentScriptsDigest blake2b256
      (inputs.map (·.scriptSig cs))).toList := by
  by_cases he : inputs.isEmpty && outputs.isEmpty
  · have hin : inputs = [] := by simpa using (Bool.and_eq_true_iff.mp he).1
    have hout : outputs = [] := by simpa using (Bool.and_eq_true_iff.mp he).2
    simp [hashTransparentAuth, hin, hout, Spec.transparentScriptsDigest,
      EMPTY_TRANSPARENT_AUTH_HASH_eq]
  · simp only [hashTransparentAuth, he, Bool.false_eq_true, ite_false, hasher_eq,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [forIn_yield _ _ _ (fun (a : Input) s => update s (Spec.script (a.scriptSig cs)))
      (fun a ha s => by
        obtain ⟨hcb, hlen⟩ := hi a ha
        cases a with
        | prevOut o u q =>
          have hlen' : u.length ≤ MAX_PROTOCOL_MESSAGE_LEN := by
            simpa [Input.scriptSig] using hlen
          simp [updateSerialized, serializeBytes_ok _ hlen', Input.scriptSig]
        | coinbase h d q =>
          obtain ⟨script, hs⟩ := Option.isSome_iff_exists.mp (hcb h d q rfl)
          have hlen' : script.length ≤ MAX_PROTOCOL_MESSAGE_LEN := by
            simpa [Input.scriptSig, hs] using hlen
          simp [hs, updateSerialized, serializeBytes_ok _ hlen', Input.scriptSig]),
      foldl_update_absorbed]
    simp [finalize_state_absorbed, Spec.transparentScriptsDigest, List.flatMap_map]

/-- `hash_sapling_auth` is §A.2's digest (in version 6, ZIP 229's, with the anchor when there is
    a Spend); no component is the empty one. -/
theorem hashSaplingAuth_eq (sapling : Option SaplingData) (v : Version) (f : Spec.Format)
    (hf : f.IsV6 = v.hasIronwood) :
    hashSaplingAuth sapling v = some (Spec.saplingAuthDigest blake2b256 f
      ((sapling.map SaplingData.toSpec).getD emptySapling)).toList := by
  cases sapling with
  | none =>
    cases v <;> simp_all [hashSaplingAuth, Spec.saplingAuthDigest, emptySapling,
      Version.emptySaplingAuthHash, Version.hasIronwood, EMPTY_SAPLING_V5_AUTH_HASH_eq,
      EMPTY_SAPLING_V6_AUTH_HASH_eq]
  | some s =>
    have hne : ¬(s.toSpec.spends = [] ∧ s.toSpec.outputs = []) := by
      rcases s.nonempty with h | h <;> simp [SaplingData.toSpec, h]
    simp only [hashSaplingAuth, hasher_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.map_some, Option.getD_some]
    rw [forIn_yield _ _ _ (fun (sp : SaplingSpend) st => update st sp.zkproof.toList)
      (fun _ _ _ => rfl), foldl_update_absorbed, Option.bind_some]
    rw [forIn_yield _ _ _ (fun (sp : SaplingSpend) st => update st sp.spendAuthSig.toList)
      (fun _ _ _ => rfl), foldl_update_absorbed, Option.bind_some]
    rw [forIn_yield _ _ _ (fun (o : SaplingOutput) st => update st o.zkproof.toList)
      (fun _ _ _ => rfl), foldl_update_absorbed, Option.bind_some]
    by_cases hs : s.spends = []
    · cases v <;> simp_all [update_absorbed, finalize_state_absorbed, Spec.saplingAuthDigest,
        Version.saplingAuthPersonalization, Version.saplingAuthIncludesAnchor,
        Version.hasIronwood, SaplingData.toSpec, List.flatMap_map]
    · obtain ⟨a, ha⟩ : ∃ a, s.sharedAnchor = some a := ⟨_, s.sharedAnchor_eq hs⟩
      have hs' : (!s.spends.isEmpty) = true := by simpa using hs
      cases v <;> simp only [Version.saplingAuthIncludesAnchor, Version.saplingAuthPersonalization,
          Version.hasIronwood] at hf ⊢ <;>
        simp [hs', ha, update_absorbed, finalize_state_absorbed, Spec.saplingAuthDigest, hne,
          hf] <;>
        simp [SaplingData.toSpec, List.flatMap_map, ha, hs]

/-- A format's empty auth digest is the specification's auth digest of no Actions. -/
theorem emptyAuthHash_eq (format : Format) (v6 : Bool) :
    format.emptyAuthHash = (Spec.actionsAuthDigest blake2b256 format.personalizations.toSpec v6
      emptyOrchard).toList := by
  cases format <;> simp [Format.emptyAuthHash, Spec.actionsAuthDigest, emptyOrchard,
    Format.personalizations, Orchard.Personalizations.toSpec, EMPTY_ORCHARD_V5_AUTH_HASH_eq,
    EMPTY_ORCHARD_V6_AUTH_HASH_eq, EMPTY_IRONWOOD_AUTH_HASH_eq]

/-- `hash_bundle_auth` is §A.3's digest under the format's personalization, with the anchor
    exactly when the format includes it (version 6's Orchard and Ironwood). -/
theorem hashBundleAuth_eq (bundle : Option OrchardData) (format : Format) :
    hashBundleAuth bundle format = some (Spec.actionsAuthDigest blake2b256
      format.personalizations.toSpec format.includesAnchorInAuthorizingDigest
      ((bundle.map OrchardData.toSpec).getD emptyOrchard)).toList := by
  cases bundle with
  | none => simpa [hashBundleAuth] using emptyAuthHash_eq format _
  | some b =>
    simp only [hashBundleAuth, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      update_absorbed, List.nil_append]
    rw [forIn_yield _ _ _ (fun (a : Action) st => update st a.spendAuthSig.toList)
      (fun _ _ _ => by simp [updateSerialized]), foldl_update_absorbed]
    cases format <;>
      simp [updateSerialized, update_absorbed, finalize_state_absorbed, Spec.actionsAuthDigest,
        OrchardData.toSpec, Orchard.NonEmpty.toList, List.flatMap_map, Format.personalizations,
        Orchard.Personalizations.toSpec, Format.includesAnchorInAuthorizingDigest]

/-- **Zakura's node computes the specification's auth digest** (ZIP 244 §A; for version 6,
    ZIP 229), for every version 5 or 6 transaction it parses whose coinbase `scriptSig`, if any,
    it can rebuild and whose `scriptSig`s fit in a protocol message. -/
theorem authDigest_eq (cs : CoinbaseScript) (previousOutputs : List Output) (p : Parts)
    (hi : ∀ i ∈ p.inputs, i.AuthFits cs) :
    authDigest cs p = some ((p.toSpec cs previousOutputs).authDigest blake2b256).toList := by
  have hf : (p.version.toSpec p.ironwood).IsV6 = p.version.hasIronwood := by
    cases p.version <;> rfl
  simp only [authDigest, authDigestInner, hashTransparentAuth_eq cs p.inputs p.outputs hi,
    hashSaplingAuth_eq p.sapling p.version _ hf, hashBundleAuth_eq, hasher_eq, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Spec.Transaction.authDigest, authPersonalization_eq]
  rcases p with ⟨_ | _, br, lt, eh, ins, outs, sap, orc, iw⟩ <;>
    simp [update_absorbed, finalize_state_absorbed, Version.hasIronwood, Version.orchardFormat,
      Format.includesAnchorInAuthorizingDigest, Format.personalizations,
      Orchard.Personalizations.toSpec, Parts.toSpec, Version.toSpec, Spec.Format.IsV6, Spec.node,
      Spec.orchardV5, Spec.orchardV6, Spec.ironwoodV6]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Native.authDigest_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms authDigest_eq

/--
info: 'ZcashSighash.Verifier.Native.txid_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms txid_eq

/--
info: 'ZcashSighash.Verifier.Native.EMPTY_IRONWOOD_AUTH_HASH_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EMPTY_IRONWOOD_AUTH_HASH_eq

end ZcashSighash.Verifier.Native
