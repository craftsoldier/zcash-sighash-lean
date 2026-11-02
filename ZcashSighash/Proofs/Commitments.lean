/-
What a transaction's identifier and auth digest commit to. The identifier commits to the
effecting data and ignores the authorizing data (ZIP 244: "TxId Digest"; in version 6 the anchors
are authorizing data, ZIP 229). A cache keyed by identifier alone therefore cannot tell two
transactions with different signatures or proofs apart, as Zebra's CVE-2026-34377 (GHSA-3vmh)
showed; keying it by identifier and auth digest can. Conversely, unless computing it finds a
hash collision, the identifier determines everything but the authorizing data
(`stripAuth_of_txid`).
-/
module

public import ZcashSighash.Proofs.Spec

@[expose] public section

namespace ZcashSighash.Spec

/-! ## Erasing the authorizing data -/

/-- `n` zero bytes, standing for an erased field. -/
def zeros (n : ℕ) : Bytes n := List.Vector.replicate n 0

/-- A Sapling component without its authorizing data: proofs, signatures, and in version 6 the
    anchor. The value balance and anchor are also erased where the encoding has none: the value
    balance with no Spend or Output, the anchor with no Spend. -/
def Sapling.stripAuth (v6 : Bool) (s : Sapling) : Sapling :=
  ⟨s.spends.map fun sp => ⟨sp.cv, sp.nullifier, sp.rk, zeros 192, zeros 64⟩,
    s.outputs.map fun o =>
      ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, zeros 192⟩,
    if s.spends = [] ∧ s.outputs = [] then 0 else s.valueBalance,
    if v6 ∨ s.spends = [] then zeros 32 else s.anchor, zeros 64⟩

/-- An Orchard-shaped component without its authorizing data: proofs, signatures, and in version
    6 the anchor. With no Action it is the empty component, as the encoding has no other field. -/
def OrchardBundle.stripAuth (v6 : Bool) (b : OrchardBundle) : OrchardBundle :=
  if b.actions = [] then ⟨[], 0, 0, zeros 32, [], zeros 64⟩
  else ⟨b.actions.map fun a => ⟨a.cv, a.nullifier, a.rk, a.cmx, a.ephemeralKey, a.encCiphertext,
      a.outCiphertext, zeros 64⟩, b.flags, b.valueBalance, if v6 then zeros 32 else b.anchor, [],
    zeros 64⟩

/-- The transparent inputs and outputs without the coins the inputs spend, which the transaction
    does not encode. -/
def Transparent.stripAuth (t : Transparent) : Transparent :=
  ⟨t.vin.map fun i => ⟨i.prevout, i.nSequence, ⟨0, []⟩⟩, t.vout⟩

/-- A transaction without its authorizing data, and without the coins its inputs spend. -/
def Transaction.stripAuth (tx : Transaction) : Transaction where
  format := match tx.format with
    | .v5 => .v5
    | .v6 iw => .v6 (iw.stripAuth true)
  header := tx.header
  transparent := tx.transparent.stripAuth
  scriptSigs := []
  sapling := tx.sapling.stripAuth tx.format.IsV6
  orchard := tx.orchard.stripAuth tx.format.IsV6

/-! ## The identifier ignores the authorizing data -/

section
variable (H : Hash)

/-- §T.2's digest does not see the spent coins. -/
theorem transparentDigest_stripAuth (t : Transparent) :
    transparentDigest H t.stripAuth = transparentDigest H t := by
  simp [Transparent.stripAuth, transparentDigest, prevoutsDigest, sequenceDigest, outputsDigest,
    List.flatMap_map]

/-- §T.3's digest does not see Sapling proofs or signatures, nor in version 6 the anchor. -/
theorem saplingDigest_stripAuth (f : Format) (s : Sapling) :
    saplingDigest H f (s.stripAuth f.IsV6) = saplingDigest H f s := by
  cases f <;> by_cases hs : s.spends = [] <;> by_cases ho : s.outputs = [] <;>
    simp [saplingDigest, Sapling.stripAuth, hs, ho, saplingSpendsDigest,
      saplingSpendsCompactDigest, saplingSpendsNoncompactDigest, saplingOutputsDigest,
      saplingOutputsCompactDigest, saplingOutputsMemosDigest, saplingOutputsNoncompactDigest,
      Format.IsV6, List.flatMap_map]

/-- The Sapling digest sees only whether the format is version 6, not its Ironwood Actions. -/
theorem saplingDigest_v6 (iw iw' : OrchardBundle) (s : Sapling) :
    saplingDigest H (.v6 iw) s = saplingDigest H (.v6 iw') s := by
  simp [saplingDigest, saplingSpendsDigest, saplingSpendsNoncompactDigest, Format.IsV6]

/-- §T.4's digest does not see the proofs or signatures, nor with `v6` the anchor. -/
theorem actionsDigest_stripAuth (p : Personalizations) (v6 : Bool) (b : OrchardBundle) :
    actionsDigest H p v6 (b.stripAuth v6) = actionsDigest H p v6 b := by
  by_cases ha : b.actions = []
  · simp [actionsDigest, OrchardBundle.stripAuth, ha]
  · cases v6 <;> simp [actionsDigest, OrchardBundle.stripAuth, ha, List.flatMap_map]

/-- **The identifier ignores the authorizing data**, for every hash function: erasing the
    `scriptSig`s, proofs, signatures, spent coins and (in version 6) anchors leaves it unchanged.
    So two transactions differing only there share an identifier. -/
theorem txid_stripAuth (tx : Transaction) : tx.stripAuth.txid H = tx.txid H := by
  rcases tx with ⟨_ | iw, hdr, t, ss, s, o⟩
  · have hs := saplingDigest_stripAuth H .v5 s
    simp only [Format.IsV6] at hs
    simp [Transaction.stripAuth, Transaction.txid, Transaction.version, Transaction.orchardDigest,
      Format.IsV6, txidDigest, transparentDigest_stripAuth, hs, actionsDigest_stripAuth]
  · have hs := saplingDigest_stripAuth H (.v6 iw) s
    simp only [Format.IsV6] at hs
    simp [Transaction.stripAuth, Transaction.txid, Transaction.version, Transaction.orchardDigest,
      Format.IsV6, txidDigest, transparentDigest_stripAuth,
      saplingDigest_v6 H (iw.stripAuth true) iw, hs, actionsDigest_stripAuth]

end

/-! ## The identifier commits to the rest -/

/-- Lists whose images under `f` agree have agreeing images under any `h` that `f` determines. -/
theorem map_eq_of_map {α β γ : Type} {l₁ l₂ : List α} {f : α → β} (h : α → γ)
    (hf : l₁.map f = l₂.map f) (hd : ∀ x y, f x = f y → h x = h y) : l₁.map h = l₂.map h := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l ih =>
    cases l₂ with
    | nil => simp at hf
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at hf ⊢
      exact ⟨hd _ _ hf.1, ih hf.2⟩

/-- Two agreeing images make an agreeing image of pairs. -/
theorem map_pair {α β γ : Type} {l₁ l₂ : List α} {f : α → β} {g : α → γ}
    (hf : l₁.map f = l₂.map f) (hg : l₁.map g = l₂.map g) :
    l₁.map (fun x => (f x, g x)) = l₂.map (fun x => (f x, g x)) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a l ih =>
    cases l₂ with
    | nil => simp at hf
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at hf hg ⊢
      exact ⟨by rw [hf.1, hg.1], ih hf.2 hg.2⟩

/-- A run of fixed-length byte vectors splits back into them. -/
theorem vectors_injective (n : ℕ) (hn : 0 < n) {l₁ l₂ : List (Bytes n)}
    (h : l₁.flatMap (·.toList) = l₂.flatMap (·.toList)) : l₁ = l₂ :=
  flatMap_injective_of_length List.Vector.toList n hn (by simp) List.Vector.toList_injective h

/-- A run of concatenated pairs of byte vectors splits back into the pairs. -/
theorem pairs_injective (m n : ℕ) (hmn : 0 < m + n) {l₁ l₂ : List (Bytes m × Bytes n)}
    (h : l₁.flatMap (fun p => p.1.toList ++ p.2.toList) =
      l₂.flatMap (fun p => p.1.toList ++ p.2.toList)) : l₁ = l₂ :=
  flatMap_injective_of_length (fun p : Bytes m × Bytes n => p.1.toList ++ p.2.toList) (m + n)
    hmn (by simp) (fun a b hab => by
      obtain ⟨h1, h2⟩ := List.append_inj hab (by simp)
      exact Prod.ext (List.Vector.toList_injective h1) (List.Vector.toList_injective h2)) h

/-- A run of fixed-length chunks splits back into the chunks. -/
theorem flatMap_map_eq {α : Type} {l₁ l₂ : List α} (f : α → List Byte) (k : ℕ) (hk : 0 < k)
    (hl : ∀ a, (f a).length = k) (h : l₁.flatMap f = l₂.flatMap f) : l₁.map f = l₂.map f := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons a l => have := congrArg List.length h; simp [hl] at this; omega
  | cons a l ih =>
    cases l₂ with
    | nil => have := congrArg List.length h; simp [hl] at this; omega
    | cons a' l' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨ha, hrest⟩ := List.append_inj h (by simp [hl])
      simp [ha, ih hrest]

/-- A ciphertext is its first 52 bytes, the next 512, and the rest after 564. -/
theorem encCiphertext_split {a b : Bytes 580} (h₁ : a.toList.take 52 = b.toList.take 52)
    (h₂ : (a.toList.drop 52).take 512 = (b.toList.drop 52).take 512)
    (h₃ : a.toList.drop 564 = b.toList.drop 564) : a = b := by
  apply List.Vector.toList_injective
  rw [← List.take_append_drop 52 a.toList, ← List.take_append_drop 52 b.toList,
    ← List.take_append_drop 512 (a.toList.drop 52), ← List.take_append_drop 512 (b.toList.drop 52),
    List.drop_drop, List.drop_drop, h₁, h₂, h₃]

/-! ### The inputs each digest hashes (`CollisionFreeOn`, `Proofs/Spec.lean`) -/

/-- Collision-freedom on a set holds on its subsets. -/
theorem CollisionFreeOn.mono {H : Hash} {S T : List (Personalization × List Byte)}
    (hH : CollisionFreeOn H S) (hT : ∀ a ∈ T, a ∈ S) : CollisionFreeOn H T :=
  fun _ _ _ _ h₁ h₂ h => hH _ _ _ _ (hT _ h₁) (hT _ h₂) h

/-- Collision-freedom on two transactions' inputs holds on two of their components' inputs. -/
theorem CollisionFreeOn.both {H : Hash} {S₁ S₂ T₁ T₂ : List (Personalization × List Byte)}
    (hH : CollisionFreeOn H (S₁ ++ S₂)) (h₁ : ∀ a ∈ T₁, a ∈ S₁) (h₂ : ∀ a ∈ T₂, a ∈ S₂) :
    CollisionFreeOn H (T₁ ++ T₂) :=
  hH.mono fun a ha => by
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (h₁ a h)
    · exact List.mem_append_right _ (h₂ a h)

section
variable (H : Hash)

/-- The input §T.1 hashes. -/
def headerInputs (h : Header) : List (Personalization × List Byte) :=
  [(personal "ZTxIdHeadersHash", u32 h.version ++ u32 h.versionGroupId ++
    u32 h.consensusBranchId ++ u32 h.lockTime ++ u32 h.expiryHeight)]

/-- The inputs §T.2 hashes. -/
def transparentInputs (t : Transparent) : List (Personalization × List Byte) :=
  [(personal "ZTxIdTranspaHash", []),
    (personal "ZTxIdTranspaHash", [prevoutsDigest H t, sequenceDigest H t,
      outputsDigest H t].flatMap (·.toList)),
    (personal "ZTxIdPrevoutHash", t.vin.flatMap (·.prevout.encode)),
    (personal "ZTxIdSequencHash", t.vin.flatMap (u32 ·.nSequence)),
    (personal "ZTxIdOutputsHash", t.vout.flatMap TxOut.encode)]

/-- The inputs §T.3a hashes, in either version. -/
def saplingSpendsInputs (f : Format) (s : Sapling) : List (Personalization × List Byte) :=
  [(personal "ZTxIdSSpendsHash", []),
    (personal "ZTxIdSSpendsHash", [saplingSpendsCompactDigest H s,
      saplingSpendsNoncompactDigest H f s].flatMap (·.toList)),
    (personal "ZTxIdSSpendCHash", s.spends.flatMap (·.nullifier.toList)),
    (personal "ZTxIdSSpendNH_v6", s.spends.flatMap fun sp => sp.cv.toList ++ sp.rk.toList),
    (personal "ZTxIdSSpendNHash",
      s.spends.flatMap fun sp => sp.cv.toList ++ s.anchor.toList ++ sp.rk.toList)]

/-- The inputs §T.3b hashes. -/
def saplingOutputsInputs (s : Sapling) : List (Personalization × List Byte) :=
  [(personal "ZTxIdSOutputHash", []),
    (personal "ZTxIdSOutputHash", [saplingOutputsCompactDigest H s,
      saplingOutputsMemosDigest H s, saplingOutputsNoncompactDigest H s].flatMap (·.toList)),
    (personal "ZTxIdSOutC__Hash", s.outputs.flatMap fun o =>
      o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52),
    (personal "ZTxIdSOutM__Hash", s.outputs.flatMap fun o =>
      (o.encCiphertext.toList.drop 52).take 512),
    (personal "ZTxIdSOutN__Hash", s.outputs.flatMap fun o =>
      o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)]

/-- The inputs §T.3 hashes. -/
def saplingInputs (f : Format) (s : Sapling) : List (Personalization × List Byte) :=
  [(personal "ZTxIdSaplingHash", []),
    (personal "ZTxIdSaplingHash", (saplingSpendsDigest H f s).toList ++
      (saplingOutputsDigest H s).toList ++ i64 s.valueBalance)] ++
  saplingSpendsInputs H f s ++ saplingOutputsInputs H s

/-- The inputs §T.4 hashes, with the personalizations `p`. -/
def actionsInputs (p : Personalizations) (v6 : Bool) (b : OrchardBundle) :
    List (Personalization × List Byte) :=
  let compact := b.actions.flatMap fun a => a.nullifier.toList ++ a.cmx.toList ++
    a.ephemeralKey.toList ++ a.encCiphertext.toList.take 52
  let memos := b.actions.flatMap fun a => (a.encCiphertext.toList.drop 52).take 512
  let noncompact := b.actions.flatMap fun a => a.cv.toList ++ a.rk.toList ++
    a.encCiphertext.toList.drop 564 ++ a.outCiphertext.toList
  [(p.bundle, []),
    (p.bundle, (H p.compact compact).toList ++ (H p.memos memos).toList ++
      (H p.noncompact noncompact).toList ++
      b.flags :: i64 b.valueBalance ++ if v6 then [] else b.anchor.toList),
    (p.compact, compact), (p.memos, memos), (p.noncompact, noncompact)]

/-- The inputs the identifier hashes: its root, and each component's. -/
def txidInputs (tx : Transaction) : List (Personalization × List Byte) :=
  (txHashPersonalization tx.header.consensusBranchId,
    (([headerDigest H tx.header, transparentDigest H tx.transparent,
      saplingDigest H tx.format tx.sapling, tx.orchardDigest H] ++
      match tx.version H with | .v5 => [] | .v6 ironwood => [ironwood]).flatMap (·.toList))) ::
  headerInputs tx.header ++ transparentInputs H tx.transparent ++
    saplingInputs H tx.format tx.sapling ++ actionsInputs H orchardV5 false tx.orchard ++
    actionsInputs H orchardV6 true tx.orchard ++
    match tx.format with | .v5 => [] | .v6 iw => actionsInputs H ironwoodV6 true iw

end

/-- The Sapling inputs see only whether the format is version 6. -/
theorem saplingInputs_v6 (H : Hash) (iw iw' : OrchardBundle) (s : Sapling) :
    saplingInputs H (.v6 iw) s = saplingInputs H (.v6 iw') s := by
  simp [saplingInputs, saplingSpendsInputs, saplingSpendsDigest, saplingSpendsNoncompactDigest,
    Format.IsV6]

/-- The header digest determines the header. -/
theorem header_of_digest (H : Hash) {h₁ h₂ : Header}
    (hH : CollisionFreeOn H (headerInputs h₁ ++ headerInputs h₂))
    (heq : headerDigest H h₁ = headerDigest H h₂) : h₁ = h₂ := by
  unfold headerDigest at heq
  have h := hH.eq (by simp [headerInputs]) (by simp [headerInputs]) heq
  obtain ⟨_, _, _, _, _⟩ := h₁
  obtain ⟨_, _, _, _, _⟩ := h₂
  simp only [List.append_assoc] at h
  obtain ⟨a, h⟩ := List.append_inj h (by simp [u32_length])
  obtain ⟨b, h⟩ := List.append_inj h (by simp [u32_length])
  obtain ⟨c, h⟩ := List.append_inj h (by simp [u32_length])
  obtain ⟨d, e⟩ := List.append_inj h (by simp [u32_length])
  rw [u32_injective a, u32_injective b, u32_injective c, u32_injective d, u32_injective e]

/-- §T.2's digest determines the transparent part, without the spent coins, when the output
    scripts fit a `compactSize`. -/
theorem transparent_of_digest (H : Hash) {t₁ t₂ : Transparent}
    (hH : CollisionFreeOn H (transparentInputs H t₁ ++ transparentInputs H t₂))
    (ho₁ : ∀ o ∈ t₁.vout, o.scriptPubKey.length < 2 ^ 64)
    (ho₂ : ∀ o ∈ t₂.vout, o.scriptPubKey.length < 2 ^ 64)
    (heq : transparentDigest H t₁ = transparentDigest H t₂) : t₁.stripAuth = t₂.stripAuth := by
  unfold transparentDigest at heq
  split_ifs at heq with he₁ he₂ he₂
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at he₁ he₂
    simp [Transparent.stripAuth, he₁, he₂]
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [transparentInputs]) (by simp [transparentInputs]) heq)
    simp at this
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [transparentInputs]) (by simp [transparentInputs]) heq)
    simp at this
  · have hc := node_eq hH (by simp [transparentInputs]) (by simp [transparentInputs]) heq
    simp only [List.cons.injEq, and_true] at hc
    obtain ⟨hp, hq, hout⟩ := hc
    unfold prevoutsDigest at hp
    unfold sequenceDigest at hq
    unfold outputsDigest at hout
    have hp := hH.eq (by simp [transparentInputs]) (by simp [transparentInputs]) hp
    have hq := hH.eq (by simp [transparentInputs]) (by simp [transparentInputs]) hq
    have hout := hH.eq (by simp [transparentInputs]) (by simp [transparentInputs]) hout
    have hp' : t₁.vin.map (·.prevout) = t₂.vin.map (·.prevout) :=
      flatMap_injective_of_length OutPoint.encode 36 (by decide) OutPoint.encode_length
        OutPoint.encode_injective (by simpa [List.flatMap_map] using hp)
    have hq' : t₁.vin.map (·.nSequence) = t₂.vin.map (·.nSequence) :=
      flatMap_injective_of_length u32 4 (by decide) u32_length u32_injective
        (by simpa [List.flatMap_map] using hq)
    have hout' : t₁.vout = t₂.vout := TxOut.encode_flatMap_injective _ _ ho₁ ho₂ hout
    have hvin := map_eq_of_map (fun i : TxIn => (⟨i.prevout, i.nSequence, ⟨0, []⟩⟩ : TxIn))
      (map_pair hp' hq') (fun x y hxy => by simp_all)
    simp only [Transparent.stripAuth, hout', Transparent.mk.injEq, and_true]
    exact hvin

/-- §T.3b's digest determines the Sapling Outputs, without their proofs. -/
theorem saplingOutputs_of_digest (H : Hash) {s₁ s₂ : Sapling}
    (hH : CollisionFreeOn H (saplingOutputsInputs H s₁ ++ saplingOutputsInputs H s₂))
    (heq : saplingOutputsDigest H s₁ = saplingOutputsDigest H s₂) :
    s₁.outputs.map (fun o => (⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext,
        zeros 192⟩ : SaplingOutput)) =
      s₂.outputs.map (fun o => ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext,
        zeros 192⟩) := by
  unfold saplingOutputsDigest at heq
  split_ifs at heq with h₁ h₂ h₂
  · simp [h₁, h₂]
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) heq)
    simp at this
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) heq)
    simp at this
  · have hc := node_eq hH (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) heq
    simp only [List.cons.injEq, and_true] at hc
    obtain ⟨hc, hm, hn⟩ := hc
    unfold saplingOutputsCompactDigest at hc
    unfold saplingOutputsMemosDigest at hm
    unfold saplingOutputsNoncompactDigest at hn
    have hc := hH.eq (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) hc
    have hm := hH.eq (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) hm
    have hn := hH.eq (by simp [saplingOutputsInputs]) (by simp [saplingOutputsInputs]) hn
    have hc' := flatMap_map_eq (fun o : SaplingOutput => o.cmu.toList ++ o.ephemeralKey.toList ++
      o.encCiphertext.toList.take 52) 116 (by decide) (by simp) hc
    have hm' := flatMap_map_eq (fun o : SaplingOutput => (o.encCiphertext.toList.drop 52).take 512)
      512 (by decide) (by simp) hm
    have hn' := flatMap_map_eq (fun o : SaplingOutput => o.cv.toList ++
      o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList) 128 (by decide) (by simp) hn
    refine map_eq_of_map _ (map_pair (map_pair hc' hm') hn') fun x y hxy => ?_
    simp only [Prod.mk.injEq, List.append_assoc] at hxy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
    obtain ⟨hcmu, h1⟩ := List.append_inj h1 (by simp)
    obtain ⟨hepk, h1⟩ := List.append_inj h1 (by simp)
    obtain ⟨hcv, h3⟩ := List.append_inj h3 (by simp)
    obtain ⟨h3, hout⟩ := List.append_inj h3 (by simp)
    simp [List.Vector.toList_injective hcmu, List.Vector.toList_injective hepk,
      List.Vector.toList_injective hcv, List.Vector.toList_injective hout,
      encCiphertext_split h1 h2 h3]

/-- §T.3a's digest determines the Sapling Spends, without their proofs and signatures, and in
    version 5, when there is a Spend, the anchor. -/
theorem saplingSpends_of_digest (H : Hash) (f : Format) {s₁ s₂ : Sapling}
    (hH : CollisionFreeOn H (saplingSpendsInputs H f s₁ ++ saplingSpendsInputs H f s₂))
    (heq : saplingSpendsDigest H f s₁ = saplingSpendsDigest H f s₂) :
    s₁.spends.map (fun sp => (⟨sp.cv, sp.nullifier, sp.rk, zeros 192, zeros 64⟩ : SaplingSpend)) =
        s₂.spends.map (fun sp => ⟨sp.cv, sp.nullifier, sp.rk, zeros 192, zeros 64⟩) ∧
      (f.IsV6 = false → s₁.spends ≠ [] → s₁.anchor = s₂.anchor) := by
  unfold saplingSpendsDigest at heq
  split_ifs at heq with h₁ h₂ h₂
  · simp [h₁, h₂]
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) heq)
    simp at this
  · unfold node at heq
    have := congrArg List.length
      (hH.eq (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) heq)
    simp at this
  · have hc := node_eq hH (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) heq
    simp only [List.cons.injEq, and_true] at hc
    obtain ⟨hc, hn⟩ := hc
    unfold saplingSpendsCompactDigest at hc
    have hc := hH.eq (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) hc
    have hc' := flatMap_map_eq (fun sp : SaplingSpend => sp.nullifier.toList) 32 (by decide)
      (by simp) hc
    -- The noncompact digest: each Spend's `cv` and `rk`, and in version 5 the anchor.
    have hn' : s₁.spends.map (fun sp => (sp.cv, sp.rk)) = s₂.spends.map (fun sp => (sp.cv, sp.rk)) ∧
        (f.IsV6 = false → s₁.anchor = s₂.anchor) := by
      unfold saplingSpendsNoncompactDigest at hn
      cases f with
      | v6 =>
        simp only [Format.IsV6, ite_true] at hn
        have hn := hH.eq (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) hn
        refine ⟨pairs_injective 32 32 (by decide) ?_, by simp [Format.IsV6]⟩
        simpa [List.flatMap_map] using hn
      | v5 =>
        simp only [Format.IsV6, Bool.false_eq_true, ite_false] at hn
        have hn := hH.eq (by simp [saplingSpendsInputs]) (by simp [saplingSpendsInputs]) hn
        have h3 := flatMap_injective_of_length
          (fun t : Bytes 32 × Bytes 32 × Bytes 32 => t.1.toList ++ t.2.1.toList ++ t.2.2.toList)
          96 (by decide) (by simp) (fun a b hab => by
            obtain ⟨h1, h2⟩ := List.append_inj (by simpa only [List.append_assoc] using hab)
              (by simp)
            obtain ⟨h2, h3⟩ := List.append_inj h2 (by simp)
            exact Prod.ext (List.Vector.toList_injective h1)
              (Prod.ext (List.Vector.toList_injective h2) (List.Vector.toList_injective h3)))
          (a₁ := s₁.spends.map fun sp => (sp.cv, s₁.anchor, sp.rk))
          (a₂ := s₂.spends.map fun sp => (sp.cv, s₂.anchor, sp.rk))
          (by simpa [List.flatMap_map] using hn)
        refine ⟨by simpa [Function.comp_def] using congrArg (List.map fun t => (t.1, t.2.2)) h3,
          fun _ => ?_⟩
        obtain ⟨a, l, ha⟩ := List.exists_cons_of_ne_nil h₁
        obtain ⟨b, l', hb⟩ := List.exists_cons_of_ne_nil h₂
        simp [ha, hb] at h3
        exact h3.1.2.1
    refine ⟨map_eq_of_map _ (map_pair hc' hn'.1) fun x y hxy => ?_, fun hf _ => hn'.2 hf⟩
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    simp [List.Vector.toList_injective h1, h2, h3]

/-- §T.3's digest determines the Sapling component, without its authorizing data. -/
theorem sapling_of_digest (H : Hash) (f : Format) {s₁ s₂ : Sapling}
    (hH : CollisionFreeOn H (saplingInputs H f s₁ ++ saplingInputs H f s₂))
    (heq : saplingDigest H f s₁ = saplingDigest H f s₂) :
    s₁.stripAuth f.IsV6 = s₂.stripAuth f.IsV6 := by
  unfold saplingDigest at heq
  split_ifs at heq with h₁ h₂ h₂
  · simp [Sapling.stripAuth, h₁, h₂]
  · have := congrArg List.length
      (hH.eq (by simp [saplingInputs]) (by simp [saplingInputs]) heq)
    simp [i64_length] at this
  · have := congrArg List.length
      (hH.eq (by simp [saplingInputs]) (by simp [saplingInputs]) heq)
    simp [i64_length] at this
  · have h := hH.eq (by simp [saplingInputs]) (by simp [saplingInputs]) heq
    obtain ⟨hsp, h⟩ := List.append_inj (by simpa only [List.append_assoc] using h) (by simp)
    obtain ⟨hout, hvb⟩ := List.append_inj h (by simp)
    obtain ⟨hsp', han⟩ := saplingSpends_of_digest H f
      (hH.both (fun a ha => by simp [saplingInputs, ha]) (fun a ha => by simp [saplingInputs, ha]))
      (List.Vector.toList_injective hsp)
    have hout' := saplingOutputs_of_digest H
      (hH.both (fun a ha => by simp [saplingInputs, ha]) (fun a ha => by simp [saplingInputs, ha]))
      (List.Vector.toList_injective hout)
    have hlen : s₁.spends = [] ↔ s₂.spends = [] := by
      rw [← List.map_eq_nil_iff, hsp', List.map_eq_nil_iff]
    simp only [Sapling.stripAuth, hsp', hout', h₁, h₂, ite_false, i64_injective hvb,
      Sapling.mk.injEq, true_and, and_true]
    by_cases hv : f.IsV6 <;> by_cases he : s₁.spends = [] <;> simp_all

/-- §T.4's digest determines an Orchard-shaped component, without its authorizing data. -/
theorem actions_of_digest (H : Hash) (p : Personalizations) (v6 : Bool)
    {b₁ b₂ : OrchardBundle}
    (hH : CollisionFreeOn H (actionsInputs H p v6 b₁ ++ actionsInputs H p v6 b₂))
    (heq : actionsDigest H p v6 b₁ = actionsDigest H p v6 b₂) :
    b₁.stripAuth v6 = b₂.stripAuth v6 := by
  unfold actionsDigest at heq
  by_cases h₁ : b₁.actions = [] <;> by_cases h₂ : b₂.actions = [] <;>
    simp only [h₁, h₂, ite_true, ite_false] at heq
  · simp [OrchardBundle.stripAuth, h₁, h₂]
  · have := congrArg List.length
      (hH.eq (by simp [actionsInputs]) (by simp [actionsInputs]) heq)
    simp [i64_length] at this
  · have := congrArg List.length
      (hH.eq (by simp [actionsInputs]) (by simp [actionsInputs]) heq)
    simp [i64_length] at this
  · have h := hH.eq (by simp [actionsInputs]) (by simp [actionsInputs]) heq
    simp only [List.append_assoc] at h
    obtain ⟨hc, h⟩ := List.append_inj h (by simp)
    obtain ⟨hm, h⟩ := List.append_inj h (by simp)
    obtain ⟨hn, h⟩ := List.append_inj h (by simp)
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hfl, h⟩ := h
    obtain ⟨hvb, han⟩ := List.append_inj h (by simp [i64_length])
    have hc' := flatMap_map_eq (fun a : Action => a.nullifier.toList ++ (a.cmx.toList ++
      (a.ephemeralKey.toList ++ a.encCiphertext.toList.take 52))) 148 (by decide) (by simp)
      (hH.eq (by simp [actionsInputs]) (by simp [actionsInputs])
        (List.Vector.toList_injective hc))
    have hm' := flatMap_map_eq (fun a : Action => (a.encCiphertext.toList.drop 52).take 512)
      512 (by decide) (by simp)
      (hH.eq (by simp [actionsInputs]) (by simp [actionsInputs])
        (List.Vector.toList_injective hm))
    have hn' := flatMap_map_eq (fun a : Action => a.cv.toList ++ (a.rk.toList ++
      (a.encCiphertext.toList.drop 564 ++ a.outCiphertext.toList))) 160 (by decide) (by simp)
      (hH.eq (by simp [actionsInputs]) (by simp [actionsInputs])
        (List.Vector.toList_injective hn))
    have hacts := map_eq_of_map (fun a : Action => (⟨a.cv, a.nullifier, a.rk, a.cmx,
        a.ephemeralKey, a.encCiphertext, a.outCiphertext, zeros 64⟩ : Action))
      (map_pair (map_pair hc' hm') hn') fun x y hxy => by
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
        obtain ⟨hnf, h1⟩ := List.append_inj h1 (by simp)
        obtain ⟨hcmx, h1⟩ := List.append_inj h1 (by simp)
        obtain ⟨hepk, h1⟩ := List.append_inj h1 (by simp)
        obtain ⟨hcv, h3⟩ := List.append_inj h3 (by simp)
        obtain ⟨hrk, h3⟩ := List.append_inj h3 (by simp)
        obtain ⟨h3, hout⟩ := List.append_inj h3 (by simp)
        simp [List.Vector.toList_injective hnf, List.Vector.toList_injective hcmx,
          List.Vector.toList_injective hepk, List.Vector.toList_injective hcv,
          List.Vector.toList_injective hrk, List.Vector.toList_injective hout,
          encCiphertext_split h1 h2 h3]
    simp only [OrchardBundle.stripAuth, h₁, h₂, ite_false, hacts, hfl, i64_injective hvb]
    cases v6
    · simp at han; simp [List.Vector.toList_injective han]
    · rfl

/-- **The identifier commits to everything but the authorizing data** (ZIP 244, "TxId Digest";
    ZIP 229): two transactions with the same identifier are the same once their authorizing data
    and spent coins are erased, unless computing their identifiers hashes two different inputs to
    one digest, when their output scripts fit a `compactSize`. With `txid_stripAuth`, the
    identifier commits to exactly the erased transaction. -/
theorem stripAuth_of_txid (H : Hash) {tx₁ tx₂ : Transaction}
    (hH : CollisionFreeOn H (txidInputs H tx₁ ++ txidInputs H tx₂))
    (ho₁ : ∀ o ∈ tx₁.transparent.vout, o.scriptPubKey.length < 2 ^ 64)
    (ho₂ : ∀ o ∈ tx₂.transparent.vout, o.scriptPubKey.length < 2 ^ 64)
    (heq : tx₁.txid H = tx₂.txid H) : tx₁.stripAuth = tx₂.stripAuth := by
  unfold Transaction.txid txidDigest node at heq
  have hd := vectors_injective 32 (by decide) (hH _ _ _ _
    (List.mem_append_left _ List.mem_cons_self) (List.mem_append_right _ List.mem_cons_self)
    heq).2
  rcases tx₁ with ⟨_ | iw₁, hd₁, t₁, ss₁, s₁, o₁⟩ <;>
    rcases tx₂ with ⟨_ | iw₂, hd₂, t₂, ss₂, s₂, o₂⟩ <;>
    simp only [Transaction.version, List.cons_append, List.nil_append, List.cons.injEq,
      and_true, List.append_nil, reduceCtorEq, and_false, List.cons_ne_nil] at hd
  · obtain ⟨hh, ht, hs, ho⟩ := hd
    have hs' := sapling_of_digest H .v5
      (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) hs
    have ho' := actions_of_digest H _ _
      (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) ho
    simp only [Transaction.stripAuth, Format.IsV6] at hs' ho' ⊢
    rw [header_of_digest H
        (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) hh,
      transparent_of_digest H
        (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha]))
        ho₁ ho₂ ht, hs', ho']
  · obtain ⟨hh, ht, hs, ho, hiw⟩ := hd
    rw [saplingDigest_v6 H iw₂ iw₁] at hs
    have hs' := sapling_of_digest H (.v6 iw₁)
      (hH.both (fun a ha => by simp [txidInputs, ha])
        (fun a ha => by rw [saplingInputs_v6 H iw₁ iw₂] at ha; simp [txidInputs, ha])) hs
    have ho' := actions_of_digest H _ _
      (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) ho
    have hiw' := actions_of_digest H _ _
      (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) hiw
    simp only [Transaction.stripAuth, Format.IsV6] at hs' ho' ⊢
    rw [header_of_digest H
        (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha])) hh,
      transparent_of_digest H
        (hH.both (fun a ha => by simp [txidInputs, ha]) (fun a ha => by simp [txidInputs, ha]))
        ho₁ ho₂ ht, hs', ho', hiw']

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Spec.txid_stripAuth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms txid_stripAuth

/--
info: 'ZcashSighash.Spec.stripAuth_of_txid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stripAuth_of_txid

end ZcashSighash.Spec
