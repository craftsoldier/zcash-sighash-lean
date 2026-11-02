/-
What Zebra's signature digests are. Its rebuild of a transaction keeps every field but the
consensus branch ID, which becomes the network upgrade's, and the transparent authorization,
which becomes the coins its inputs spend (`fromTransactionWithBranchId_eq`), given that the
transaction has no bundle the rebuild drops, as none `Transaction::read` returns does. For a
version 5 or 6 transaction, the network upgrade's branch ID must be the transaction's own
(`precomputedTxData_new_mismatch`), so the rebuild changes only the authorization, and `sighash`
gives the specification's signature digest of the transaction spending those coins
(`sighash_shielded_eq`, `sighash_transparent_eq`).
-/
module

public import ZcashSighash.Proofs.Read
public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Verifier.Zebra

@[expose] public section

namespace ZcashSighash.Verifier.Zebra

/-- The transaction with consensus branch ID `branchId`, its transparent inputs spending
    `allPreviousOutputs`. -/
def rebuilt (tx : TransactionData) (branchId : BitVec 32)
    (allPreviousOutputs : List Output) : TransactionData :=
  { tx with
    consensusBranchId := branchId
    transparentBundle := tx.transparentBundle.map fun b =>
      { b with authorization := transparentAuth allPreviousOutputs } }

/-- Zebra's identity maps leave a Sapling bundle unchanged. -/
theorem sapling_mapAuthorization_identity (b : Sapling.Bundle) :
    b.mapAuthorization identityMapSapling = b := by
  rcases b with ⟨spends, outputs, vb, sig⟩
  simp only [Sapling.Bundle.mapAuthorization, identityMapSapling, Sapling.Bundle.mk.injEq,
    and_true]
  exact ⟨List.map_id'' (fun _ => rfl) _, List.map_id'' (fun _ => rfl) _⟩

/-- Zebra's identity maps leave an Orchard-shaped bundle unchanged. -/
theorem orchard_mapAuthorization_identity (b : Orchard.Bundle) :
    b.mapAuthorization identityMapOrchard = b := by
  have ha (a : Orchard.Action) :
      Orchard.Bundle.mapAuthorization.mapAction identityMapOrchard a = a := rfl
  rcases b with ⟨⟨a, as⟩, flags, vb, anchor, proof, sig, pool⟩
  simp only [Orchard.Bundle.mapAuthorization, ha, List.map_id'' ha]
  rfl

/-- Zebra's transparent map keeps each input and output and replaces the authorization. -/
theorem transparent_mapAuthorization (b : Transparent.Bundle)
    (auth : Transparent.AuthorizingContext) :
    b.mapAuthorization (mapTransparent auth) = { b with authorization := auth } := by
  rcases b with ⟨vin, vout, a⟩
  simp [Transparent.Bundle.mapAuthorization, mapTransparent]

/-- **Zebra's rebuild keeps every field of a transaction but its consensus branch ID and
    transparent authorization**, when it has no bundle the rebuild drops: no Sprout bundle in
    version 6, no Ironwood bundle before it. -/
theorem rebuild_eq (tx : TransactionData) (branchId : BitVec 32)
    (allPreviousOutputs : List Output)
    (hs : tx.version = .v6 → tx.sproutBundle = none)
    (hi : tx.version ≠ .v6 → tx.ironwoodBundle = none) :
    (transactionDataFromParts tx.version branchId tx.lockTime tx.expiryHeight
        tx.transparentBundle tx.sproutBundle tx.saplingBundle tx.orchardBundle
        tx.ironwoodBundle).mapAuthorization
      (mapTransparent (transparentAuth allPreviousOutputs)) identityMapSapling
      identityMapOrchard = rebuilt tx branchId allPreviousOutputs := by
  rcases tx with ⟨v, br, lt, eh, t, sp, sa, o, iw⟩
  cases v <;>
  simp_all [transactionDataFromParts, TransactionData.fromParts, TransactionData.fromPartsV6,
    TransactionData.mapAuthorization, rebuilt, transparent_mapAuthorization,
    sapling_mapAuthorization_identity, orchard_mapAuthorization_identity]

/-- `from_transaction_with_branch_id` computes the digests of the rebuilt transaction. -/
theorem fromTransactionWithBranchId_eq (tx : TransactionData) (branchId : BitVec 32)
    (allPreviousOutputs : List Output)
    (hs : tx.version = .v6 → tx.sproutBundle = none)
    (hi : tx.version ≠ .v6 → tx.ironwoodBundle = none) :
    fromTransactionWithBranchId tx branchId allPreviousOutputs =
      (PrecomputedSighashData.new (rebuilt tx branchId allPreviousOutputs)).map
        (⟨·, allPreviousOutputs⟩) := by
  unfold fromTransactionWithBranchId
  simp only
  rw [rebuild_eq tx branchId allPreviousOutputs hs hi]
  cases PrecomputedSighashData.new (rebuilt tx branchId allPreviousOutputs) <;> rfl

/-- For a version 5 or 6 transaction, `PrecomputedSighashData::new` computes what `new_zip244`
    does. -/
theorem new_eq_newZip244 (tx : TransactionData) (hv : tx.version = .v5 ∨ tx.version = .v6) :
    PrecomputedSighashData.new tx = (PrecomputedSighashData.newZip244 tx).bind
      fun d => d.map .zip244 := by
  unfold PrecomputedSighashData.new PrecomputedSighashData.newZip244
  rcases hv with hv | hv <;> rw [hv] <;>
  · cases tx.txIdDigests <;> simp only [bind, Option.bind]
    cases tx.transparentBundle with
    | none => rfl
    | some b =>
      simp only
      cases TransparentInputsDigests.forBundle b <;> rfl

/-- The rebuilt transaction is `WellFormed` when the transaction is: the hypothesis reads
    neither the consensus branch ID nor the transparent authorization. -/
theorem wellFormed_rebuilt {tx : TransactionData} (h : WellFormed tx) (branchId : BitVec 32)
    (allPreviousOutputs : List Output) :
    WellFormed (rebuilt tx branchId allPreviousOutputs) := by
  obtain ⟨hv, htn, hos, hsa, hop, hip, hss, hsn⟩ := h
  refine ⟨hv, ?_, ?_, hsa, hop, hip, ?_, hsn⟩ <;>
  · intro b hb
    simp only [rebuilt, Option.map_eq_some_iff] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    first | exact htn b' hb' | exact hos b' hb' | exact hss b' hb'

/-- The coins fit a transaction: one per input, unless its transparent bundle is a coinbase or
    has no inputs, whose digests read no coin; each lock script at most `MAX_COMPACT_SIZE`
    bytes. -/
structure CoinsFit (tx : TransactionData) (allPreviousOutputs : List Output) : Prop where
  length : ∀ b, tx.transparentBundle = some b → (b.isCoinbase || b.vin.isEmpty) = false →
    allPreviousOutputs.length = b.vin.length
  scripts : ∀ o ∈ allPreviousOutputs, o.lockScript.code.length ≤ MAX_COMPACT_SIZE

/-- Coins that fit the transaction fit its rebuilt bundle where the digests read them. -/
theorem contextFits_rebuilt {tx : TransactionData} {branchId : BitVec 32}
    {allPreviousOutputs : List Output} (hf : CoinsFit tx allPreviousOutputs) :
    ∀ b, (rebuilt tx branchId allPreviousOutputs).transparentBundle = some b →
      ContextFitsIfRead b := by
  intro b hb hcb
  simp only [rebuilt, Option.map_eq_some_iff] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  have hl := hf.length b' hb' hcb
  refine ⟨by simp [transparentAuth, hl], by simp [transparentAuth, hl], ?_⟩
  intro s hs'
  simp only [transparentAuth, List.mem_map] at hs'
  obtain ⟨o, ho, rfl⟩ := hs'
  exact hf.scripts o ho

/-- A transaction `Transaction::read` returns has the bundles the rebuild keeps: no Sprout bundle,
    and an Ironwood bundle only in version 6. -/
theorem read_bundles {ctx : Transparent.AuthorizingContext} {s s' : List Spec.Byte}
    {tx : TransactionData} (h : Read.read ctx s = some (.tx tx, s')) :
    tx.sproutBundle = none ∧ (tx.version ≠ .v6 → tx.ironwoodBundle = none) := by
  obtain ⟨s₁, ⟨-, ht⟩ | ⟨-, ht⟩⟩ := Read.read_tx h
  · obtain ⟨_, s₁, -, h₁⟩ := Native.Parser.bind_eq_some.mp ht
    obtain ⟨_, s₂, -, h₂⟩ := Native.Parser.bind_eq_some.mp h₁
    obtain ⟨_, s₃, -, h₃⟩ := Native.Parser.bind_eq_some.mp h₂
    obtain ⟨_, s₄, -, h₄⟩ := Native.Parser.bind_eq_some.mp h₃
    simp only [Native.pure_apply, Option.some.injEq, Prod.mk.injEq] at h₄
    rw [← h₄.1]
    exact ⟨rfl, fun _ => rfl⟩
  · have hv := Read.readV6_version ht
    obtain ⟨_, s₁, -, h₁⟩ := Native.Parser.bind_eq_some.mp ht
    obtain ⟨_, s₂, -, h₂⟩ := Native.Parser.bind_eq_some.mp h₁
    obtain ⟨_, s₃, -, h₃⟩ := Native.Parser.bind_eq_some.mp h₂
    obtain ⟨_, s₄, -, h₄⟩ := Native.Parser.bind_eq_some.mp h₃
    obtain ⟨_, s₅, -, h₅⟩ := Native.Parser.bind_eq_some.mp h₄
    simp only [Native.pure_apply, Option.some.injEq, Prod.mk.injEq] at h₅
    rw [← h₅.1]
    exact ⟨rfl, fun hne => absurd hv (by rw [← h₅.1]; exact hne)⟩

/-- **Zebra's `PrecomputedTxData::new`, for a version 5 or 6 transaction `Transaction::read`
    returned, under the network upgrade of its own consensus branch ID, holds the specification's
    digests of that transaction spending `allPreviousOutputs`**, coins that fit it. -/
theorem precomputedTxData_new_eq {ctx : Transparent.AuthorizingContext} {s s' : List Spec.Byte}
    {tx : TransactionData} (h : Read.read ctx s = some (.tx tx, s'))
    (allPreviousOutputs : List Output) (hf : CoinsFit tx allPreviousOutputs) :
    ∃ d, PrecomputedTxData.new tx (some tx.consensusBranchId) allPreviousOutputs =
      some (.ok ⟨.zip244 ⟨rebuilt tx tx.consensusBranchId allPreviousOutputs,
        zip244DigestsOf (rebuilt tx tx.consensusBranchId allPreviousOutputs), d⟩,
        allPreviousOutputs⟩) ∧
      (∀ b, (rebuilt tx tx.consensusBranchId allPreviousOutputs).transparentBundle = some b →
        InputsDigestsFit b d) ∧
      ((rebuilt tx tx.consensusBranchId allPreviousOutputs).transparentBundle = none →
        d = none) := by
  obtain ⟨hsp, hiw⟩ := read_bundles h
  generalize hrt : rebuilt tx tx.consensusBranchId allPreviousOutputs = rt
  have hw : WellFormed rt :=
    hrt ▸ wellFormed_rebuilt (Read.read_wellFormed h) tx.consensusBranchId allPreviousOutputs
  obtain ⟨d, hd, hfit⟩ := newZip244_eq rt hw (hrt ▸ contextFits_rebuilt hf)
  refine ⟨d, ?_, hfit, fun hn => ?_⟩
  · simp only [PrecomputedTxData.new, ne_eq, not_true_eq_false, and_false, ite_false,
      fromTransactionWithBranchId_eq tx _ _ (fun _ => hsp) hiw, hrt,
      new_eq_newZip244 rt hw.version, hd]
    rfl
  · have := txIdDigests_eq rt hw
    rcases hw.version with hv | hv <;>
    simp [PrecomputedSighashData.newZip244, hv, hn, this, zip244DigestsOf] at hd <;>
    exact hd.symm

/-- **Under a network upgrade with another consensus branch ID, Zebra's `PrecomputedTxData::new`
    rejects a version 5 or 6 transaction.** -/
theorem precomputedTxData_new_mismatch (tx : TransactionData)
    (hv : tx.version = .v5 ∨ tx.version = .v6) (branchId : BitVec 32)
    (hb : tx.consensusBranchId ≠ branchId) (allPreviousOutputs : List Output) :
    PrecomputedTxData.new tx (some branchId) allPreviousOutputs =
      some (.error .invalidConsensusBranchId) := by
  have h5 : version tx.version ≥ 5 := by rcases hv with hv | hv <;> simp [hv, version]
  simp [PrecomputedTxData.new, h5, hb]

/-- Zebra's `HashType` bits of a hash type convert to the `SighashType` of its byte. -/
theorem toSighashType?_toByte (ht : Spec.HashType) :
    toSighashType? (ht.toByte.setWidth 32) = some ⟨ht.toByte⟩ := by
  rcases ht with ⟨_ | _ | _, _ | _⟩ <;> rfl

/-- The shielded signature digest is the same over equal transparent parts. -/
theorem signatureDigest_shielded_congr {t t' : Spec.Transparent} (h : t = t') (v : Spec.Version)
    (branchId : BitVec 32) (header sapling orchard : Spec.Digest) :
    Spec.signatureDigest blake2b256 v branchId header sapling orchard
        (.shielded : Spec.SignableInput t) =
      Spec.signatureDigest blake2b256 v branchId header sapling orchard
        (.shielded : Spec.SignableInput t') := by
  subst h; rfl

/-- **Zebra's shielded signature digest (no input, which Zebra computes with `HashType::ALL`) of
    a version 5 or 6 transaction `Transaction::read` returned, under the network upgrade of its
    own consensus branch ID, is the specification's**, for the transaction spending
    `allPreviousOutputs`, coins that fit it, which need none for a coinbase, as Zebra looks up
    none for it. A shielded input is hashed with
    `SIGHASH_ALL` whatever the hash type. -/
theorem sighash_shielded_eq {ctx : Transparent.AuthorizingContext} {s s' : List Spec.Byte}
    {tx : TransactionData} (h : Read.read ctx s = some (.tx tx, s'))
    (allPreviousOutputs : List Output) (hf : CoinsFit tx allPreviousOutputs)
    (ht : Spec.HashType) :
    ∃ data, PrecomputedTxData.new tx (some tx.consensusBranchId) allPreviousOutputs =
      some (.ok data) ∧ sighash data (ht.toByte.setWidth 32) none =
        some ((rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.signatureDigest
          blake2b256 .shielded).toList := by
  obtain ⟨d, hnew, hfit, hnone⟩ := precomputedTxData_new_eq h allPreviousOutputs hf
  refine ⟨_, hnew, ?_⟩
  have hw := wellFormed_rebuilt (Read.read_wellFormed h) tx.consensusBranchId allPreviousOutputs
  have hc := contextFits_rebuilt (branchId := tx.consensusBranchId) hf
  generalize rebuilt tx tx.consensusBranchId allPreviousOutputs = rt at hw hc hfit hnone
  have hsig : ((⟨rt, zip244DigestsOf rt, d⟩ : PrecomputedSighashData).signatureHash .shielded) =
      some (rt.toSpec.signatureDigest blake2b256 .shielded).toList := by
    cases hb : rt.transparentBundle with
    | none => rw [hnone hb]; exact signatureHash_noTransparent rt hw hb .shielded
    | some b =>
      rw [signatureHash_eq rt hw b hb (hc b hb) d (hfit b hb) .shielded .shielded .shielded,
        signatureDigest_shielded_congr (t' := rt.toSpec.transparent)
          (by simp [TransactionData.toSpec, hb])]
      rfl
  simp only [sighash, toSighashType?_toByte, sighashInner, Precomputed.signatureHash, hsig]
  rfl

/-- **Zebra's signature digest of transparent input `i` of a version 5 or 6 transaction
    `Transaction::read` returned, not a coinbase, under the network upgrade of its own consensus
    branch ID, with any hash type ZIP 244 defines and any script code, is the specification's**,
    for the transaction spending `allPreviousOutputs`, coins that fit it. -/
theorem sighash_transparent_eq {ctx : Transparent.AuthorizingContext} {s s' : List Spec.Byte}
    {tx : TransactionData} (h : Read.read ctx s = some (.tx tx, s'))
    (allPreviousOutputs : List Output) (hf : CoinsFit tx allPreviousOutputs)
    (b : Transparent.Bundle)
    (hb : (rebuilt tx tx.consensusBranchId allPreviousOutputs).transparentBundle = some b)
    (hcb : b.isCoinbase = false) (ht : Spec.HashType) (i : Fin b.toSpec.vin.length)
    (scriptCode : List Spec.Byte) :
    ∃ data, PrecomputedTxData.new tx (some tx.consensusBranchId) allPreviousOutputs =
      some (.ok data) ∧ sighash data (ht.toByte.setWidth 32) (some (i.val, scriptCode)) =
        some (Spec.signatureDigest blake2b256
          ((rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.version blake2b256)
          tx.consensusBranchId
          (Spec.headerDigest blake2b256
            (rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.header)
          (Spec.saplingDigest blake2b256
            (rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.format
            (rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.sapling)
          ((rebuilt tx tx.consensusBranchId allPreviousOutputs).toSpec.orchardDigest blake2b256)
          (.transparent ht i)).toList := by
  obtain ⟨d, hnew, hfit, -⟩ := precomputedTxData_new_eq h allPreviousOutputs hf
  refine ⟨_, hnew, ?_⟩
  have hw := wellFormed_rebuilt (Read.read_wellFormed h) tx.consensusBranchId allPreviousOutputs
  have hvin : ¬ i.val ≥ b.vin.length := by
    have := i.isLt
    simp only [Transparent.Bundle.toSpec, List.length_mapIdx] at this
    omega
  have hne : b.vin ≠ [] := fun he => by simp [he] at hvin
  have hc : ContextFits b := contextFits_rebuilt (branchId := tx.consensusBranchId) hf b hb
    (by simp [hcb, hne])
  -- The bundle's authorization is `allPreviousOutputs`', one coin per input.
  have hauth : b.authorization = transparentAuth allPreviousOutputs := by
    simp only [rebuilt, Option.map_eq_some_iff] at hb
    obtain ⟨_, -, rfl⟩ := hb
    rfl
  have hi : i.val < allPreviousOutputs.length := by
    have := i.isLt
    simp only [Transparent.Bundle.toSpec, List.length_mapIdx] at this
    have := hc.amounts
    simp only [hauth, transparentAuth, List.length_map] at this
    omega
  obtain ⟨o, ho⟩ : ∃ o, allPreviousOutputs[i.val]? = some o :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  have hrel : InputRel b (.transparent ⟨⟨ht.toByte⟩, i.val, ⟨scriptCode⟩, o.lockScript,
      o.value⟩) (.transparent ht i) :=
    .transparent _ ht i (Spec.HashType.ofByte?_toByte ht) rfl
      (by simp [hauth, transparentAuth, List.getD_eq_getElem?_getD, ho])
      (by simp [hauth, transparentAuth, List.getD_eq_getElem?_getD, ho])
  have hsig := signatureHash_eq _ hw b hb (fun _ => hc) d (hfit b hb) _ _ hrel
  have hbind {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl
  simp only [sighash, toSighashType?_toByte, sighashInner, Precomputed.tx, hb, ho,
    Transparent.SignableInput.fromParts, hvin, ite_false, Precomputed.signatureHash, hbind, hsig]
  rfl

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Zebra.sighash_shielded_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sighash_shielded_eq

/--
info: 'ZcashSighash.Verifier.Zebra.sighash_transparent_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sighash_transparent_eq

end ZcashSighash.Verifier.Zebra
