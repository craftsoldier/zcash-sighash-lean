/-
Zakura computes the specification's digests: under the hypotheses of `Proofs/Verifier.lean` and
`Proofs/VerifierV4.lean`, `to_txid`, `auth_commitment` and `signature_hash` of
`zakura-primitives` 4.0.0 give the transaction identifier, the authorizing data commitment and
every signature digest of a version 3 to 6 transaction. Below `MAX_COMPACT_SIZE` its writers are
librustzcash's; above it, Zakura still writes the specification's encoding where librustzcash
panics (`script_write_absorbed`).
-/
module

public import ZcashSighash.Proofs.VerifierV4
public import ZcashSighash.Verifier.Zakura

@[expose] public section

namespace ZcashSighash.Verifier.Zakura

open Spec (Byte Bytes personal)
open Verifier
/-- Up to `MAX_COMPACT_SIZE`, Zakura's `CompactSize::write` is librustzcash's. -/
theorem compactSize_eq {W : Type} [Write W] (w : W) (n : ℕ) (hn : n ≤ MAX_COMPACT_SIZE) :
    CompactSize.write w n = Verifier.CompactSize.write w n := by
  have h64 : n < 2 ^ 64 := by unfold MAX_COMPACT_SIZE at hn; omega
  simp only [CompactSize.write, Verifier.CompactSize.write, Verifier.CompactSize.writeUnbounded,
    show ¬(n > MAX_COMPACT_SIZE) from Nat.not_lt.mpr hn, ite_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]

/-- So is `Vector::write`, for a list no longer than `MAX_COMPACT_SIZE`. -/
theorem vector_eq {W E : Type} [Write W] (w : W) (l : List E) (f : W → E → IoResult W)
    (hn : l.length ≤ MAX_COMPACT_SIZE) : Vector.write w l f = Verifier.Vector.write w l f := by
  simp [Vector.write, Verifier.Vector.write, compactSize_eq w _ hn]

/-- So is `Script::write`, for a script no longer than `MAX_COMPACT_SIZE`. -/
theorem script_eq {W : Type} [Write W] (s : Transparent.Script) (w : W)
    (hs : s.code.length ≤ MAX_COMPACT_SIZE) : Script.write s w = s.write w := by
  simp [Script.write, Transparent.Script.write, vector_eq w _ _ hs]

/-- So is `TxOut::write`, for an output whose script is no longer than `MAX_COMPACT_SIZE`. -/
theorem txOut_eq {W : Type} [Write W] (o : Transparent.TxOut) (w : W)
    (hs : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) : TxOut.write o w = o.write w := by
  simp [TxOut.write, Transparent.TxOut.write, script_eq _ _ hs]

/-- Zakura writes a `compactSize` of any length as the specification encodes it. -/
theorem compactSize_absorbed (p : Bytes 16) (x : List Byte) (n : ℕ) (hn : n < 2 ^ 64) :
    CompactSize.write (absorbed p x) n =
      .ok (absorbed p (x ++ Spec.compactSize (BitVec.ofNat 64 n))) := by
  have := writeUnbounded_absorbed p x (BitVec.ofNat 64 n)
  simp only [Verifier.CompactSize.writeUnbounded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  rw [← this, CompactSize.write]

/-- Two loops over `l` are equal when their bodies agree on the elements of `l`. -/
theorem forIn_congr_mem {m : Type → Type} [Monad m] {α β : Type} (l : List α) (b : β)
    (f g : α → β → m (ForInStep β)) (h : ∀ a ∈ l, ∀ x, f a x = g a x) :
    forIn l b f = forIn l b g := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, h a List.mem_cons_self]
    congr 1; funext r; cases r with
    | done => rfl
    | yield y => exact ih y (fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Zakura's `transparent_outputs_hash` is librustzcash's, when the scripts fit in a
    `compactSize`. -/
theorem transparentOutputsHash_eq' (vout : List Transparent.TxOut)
    (hk : ∀ o ∈ vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    transparentOutputsHash vout = Verifier.transparentOutputsHash vout := by
  unfold transparentOutputsHash Verifier.transparentOutputsHash
  congr 1; funext h
  congr 1
  exact forIn_congr_mem _ _ _ _ fun o ho x => by simp only [txOut_eq _ _ (hk o ho)]

/-- For a well-formed transaction, Zakura's `TxIdDigester` computes librustzcash's digests. -/
theorem txIdDigests_eq' (tx : TransactionData) (h : WellFormed tx) :
    TransactionData.txIdDigests tx = tx.txIdDigests := by
  unfold TransactionData.txIdDigests Verifier.TransactionData.txIdDigests
  cases hb : tx.transparentBundle with
  | none => rfl
  | some b =>
    have e : transparentDigests b = Verifier.transparentDigests b := by
      simp only [transparentDigests, Verifier.transparentDigests,
        transparentOutputsHash_eq' _ (h.outputScripts b hb)]
    simp only [e]
    rfl

/-- In versions 5 and 6, librustzcash's `to_txid` is Zakura's, which has no version check,
    wrapped in its `Option`. -/
theorem toTxid_eq (v : TxVersion) (br : BitVec 32) (d : Zip244Digests)
    (hv : v = .v5 ∨ v = .v6) : Verifier.toTxid v br d = (toTxid v br d).map some := by
  rw [← Option.map_eq_map, map_eq_pure_bind]
  rcases hv with rfl | rfl <;>
    simp only [Verifier.toTxid, toTxid, TxVersion.hasIronwood, Bool.false_eq_true, ite_false,
      ite_true, bind_assoc]

/-- Zakura's `to_txid` gives the specification's transaction identifier. -/
theorem txid_eq (tx : TransactionData) (h : WellFormed tx) :
    (TransactionData.txIdDigests tx).bind (toTxid tx.version tx.consensusBranchId) =
      some (tx.toSpec.txid blake2b256).toList := by
  have ht := Verifier.txid_eq tx h
  rw [txIdDigests_eq' tx h]
  cases hd : tx.txIdDigests with
  | none => simp [hd] at ht
  | some d =>
    simp only [hd, Option.bind_some] at ht ⊢
    rw [toTxid_eq _ _ _ h.version] at ht
    cases hz : toTxid tx.version tx.consensusBranchId d <;> simp_all

/-- For a well-formed transaction, Zakura's transparent auth digest is librustzcash's. -/
theorem digestTransparent_eq' (tx : TransactionData) (h : WellFormed tx) :
    digestTransparent tx.transparentBundle =
      BlockTxCommitmentDigester.digestTransparent tx.transparentBundle := by
  unfold digestTransparent BlockTxCommitmentDigester.digestTransparent
  cases hb : tx.transparentBundle with
  | none => rfl
  | some b =>
    simp only
    congr 1; funext h₀
    congr 1
    exact forIn_congr_mem _ _ _ _ fun i hi x => by
      simp only [script_eq _ _ (h.scriptSigs b hb i hi)]

/-- Zakura's `auth_commitment` gives the specification's authorizing data commitment. -/
theorem authCommitment_eq (tx : TransactionData) (h : WellFormed tx) :
    TransactionData.authCommitment tx = some (tx.toSpec.authDigest blake2b256).toList := by
  rw [← Verifier.authCommitment_eq tx h]
  unfold TransactionData.authCommitment Verifier.TransactionData.authCommitment
  rw [digestTransparent_eq' tx h]

/-- Writing each amount's `to_i64_le_bytes` absorbs §S.2c's preimage. -/
theorem amounts_absorbed (p : Bytes 16) (x : List Byte) (l : List (BitVec 64)) :
    Array.write (absorbed p x) l (fun w a => w.writeAll (toLeBytes 8 a)) =
      .ok (absorbed p (x ++ l.flatMap Spec.i64)) :=
  foldlM_absorbed l p x Spec.i64 _ fun _ _ y => writeAll_absorbed p y _

/-- `amounts_absorbed` with the writer stated through `Spec.i64`, as `simp` leaves it. -/
theorem amounts_absorbed' (p : Bytes 16) (x : List Byte) (l : List (BitVec 64)) :
    Array.write (absorbed p x) l (fun w a => w.writeAll (Spec.i64 a)) =
      .ok (absorbed p (x ++ l.flatMap Spec.i64)) :=
  amounts_absorbed p x l

/-- Writing each `scriptPubKey` absorbs §S.2d's preimage, when the scripts fit in a
    `compactSize`. -/
theorem scripts_absorbed (p : Bytes 16) (x : List Byte) (l : List Transparent.Script)
    (hs : ∀ s ∈ l, s.code.length ≤ MAX_COMPACT_SIZE) :
    Array.write (absorbed p x) l (fun w s => Script.write s w) =
      .ok (absorbed p (x ++ l.flatMap (Spec.script ·.code))) :=
  foldlM_absorbed l p x (Spec.script ·.code) _ fun s h y => by
    rw [script_eq _ _ (hs s h), Verifier.Script.write_absorbed _ _ _ (hs s h)]

/-- The input digests a bundle's `ContextFits` fixes. -/
theorem amounts_spec (b : Transparent.Bundle) (hc : ContextFits b) :
    b.authorization.inputAmounts.flatMap Spec.i64 =
      b.toSpec.vin.flatMap (Spec.i64 ·.spent.value) := by
  rw [← toSpec_amounts b hc, List.flatMap_map]

/-- Likewise for the `scriptPubKey`s. -/
theorem scripts_spec (b : Transparent.Bundle) (hc : ContextFits b) :
    b.authorization.inputScriptpubkeys.flatMap (Spec.script ·.code) =
      b.toSpec.vin.flatMap (Spec.script ·.spent.scriptPubKey) := by
  have := congrArg (List.flatMap Spec.script) (toSpec_scripts b hc)
  simpa [List.flatMap_map] using this.symm

/-- Zakura's `transparent_sig_digest` of a shielded input is §S.2's digest under
    `SIGHASH_ALL`, as librustzcash's is (`Verifier.transparentSigDigest_shielded`). -/
theorem transparentSigDigest_shielded (b : Transparent.Bundle) (hc : ContextFits b)
    (hcb : ¬(b.isCoinbase || b.vin.isEmpty) = true) :
    transparentSigDigest (some (b, txidDigestsOf b)) .shielded =
      some (blake2b256 (personal "ZTxIdTranspaHash") (sigPreimage b ⟨.all, false⟩
        (Spec.outputsSigDigest blake2b256 (t := b.toSpec) .shielded)
        (Spec.txinSigDigest blake2b256 (t := b.toSpec) .shielded))).toList := by
  unfold transparentSigDigest
  simp only [(txidDigestsOf_fields b).1, (txidDigestsOf_fields b).2.1,
    (txidDigestsOf_fields b).2.2, hcb, Bool.false_eq_true, ite_false]
  simp only [SignableInput.hashType, all_flags, Bool.false_eq_true, ite_false, Bool.not_false,
    ite_true, Spec.txinSigDigest]
  simp only [hasher_pure, pure_bind, writeAll_absorbed, unwrap_pure, finalize_absorbed,
    amounts_absorbed, scripts_absorbed _ _ _ hc.scriptLength, amounts_spec b hc,
    scripts_spec b hc, List.nil_append]
  simp only [sigPreimage, Spec.prevoutsSigDigest, Spec.amountsSigDigest,
    Spec.scriptPubKeysSigDigest, Spec.sequenceSigDigest, Spec.outputsSigDigest,
    Spec.SignableInput.hashType, toByte_all, Bool.false_eq_true, ite_false, List.flatMap_cons,
    List.flatMap_nil, List.append_assoc, List.nil_append, List.cons_append, List.append_nil]
  rfl

/-- Zakura's `transparent_sig_digest` of a transparent input is §S.2's digest, as
    librustzcash's is; it computes the input digests on each call. -/
theorem transparentSigDigest_transparent (b : Transparent.Bundle)
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) (hc : ContextFits b)
    (hcb : ¬(b.isCoinbase || b.vin.isEmpty) = true) (input : Transparent.SignableInput)
    (ht : Spec.HashType)
    (i : Fin b.toSpec.vin.length) (hh : Spec.HashType.ofByte? input.hashType.byte = some ht)
    (hi : input.index = i.val) (hv : input.value = b.authorization.inputAmounts.getD i 0)
    (hs : input.scriptPubkey = b.authorization.inputScriptpubkeys.getD i ⟨[]⟩) :
    transparentSigDigest (some (b, txidDigestsOf b)) (.transparent input) =
      some (blake2b256 (personal "ZTxIdTranspaHash") (sigPreimage b ht
        (Spec.outputsSigDigest blake2b256 (Spec.SignableInput.transparent ht i))
        (Spec.txinSigDigest blake2b256 (Spec.SignableInput.transparent ht i)))).toList := by
  obtain ⟨hacp, hsingle, hnone⟩ := flags_of_ofByte? _ _ hh
  have hbyte := Spec.HashType.toByte_of_ofByte? _ _ hh
  have hlen : b.toSpec.vin.length = b.vin.length := by simp [Transparent.Bundle.toSpec]
  have hidx : input.index < b.vin.length := by have := i.isLt; omega
  have hsb : input.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := by
    rw [hs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hc.scripts]; omega),
      Option.getD_some]
    exact hc.scriptLength _ (List.getElem_mem _)
  have hi' : i.val < b.vin.length := by omega
  have hvin : b.vin[i.val]? = some b.vin[i.val] := List.getElem?_eq_getElem hi'
  have hko : ∀ (h : i.val < b.vout.length), ∀ o ∈ [b.vout[i.val]],
      o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := fun h o ho => by
    simp only [List.mem_singleton] at ho; exact ho ▸ hk _ (List.getElem_mem _)
  have htxin : b.toSpec.vin[i] = b.txinToSpec i b.vin[i.val] := by
    show (b.vin.mapIdx b.txinToSpec)[i.val]'(by simpa using hi') = _
    exact List.getElem_mapIdx
  have hon : Zakura.transparentOutputsHash [] =
      some (blake2b256 (personal "ZTxIdOutputsHash") []).toList := by
    rw [transparentOutputsHash_eq' [] (by simp)]
    simpa using Verifier.transparentOutputsHash_eq [] (by simp)
  have hos : ∀ (h : i.val < b.vout.length), Zakura.transparentOutputsHash [b.vout[i.val]] =
      some (blake2b256 (personal "ZTxIdOutputsHash")
        (Spec.i64 b.vout[i.val].value ++ Spec.script b.vout[i.val].scriptPubkey.code)).toList :=
    fun h => by
      rw [transparentOutputsHash_eq' _ (hko h)]
      simpa using Verifier.transparentOutputsHash_eq _ (hko h)
  have hpn : transparentPrevoutHash [] =
      some (blake2b256 (personal "ZTxIdPrevoutHash") []).toList := by
    simpa using transparentPrevoutHash_eq []
  have hsn : transparentSequenceHash [] =
      some (blake2b256 (personal "ZTxIdSequencHash") []).toList := by
    simpa using transparentSequenceHash_eq []
  have hvout : b.toSpec.vout = b.vout.map fun o => ⟨o.value, o.scriptPubkey.code⟩ := rfl
  obtain ⟨base, acp⟩ := ht
  cases base <;> cases acp <;>
    simp (config := {decide := true}) only [] at hacp hsingle hnone <;>
    unfold transparentSigDigest <;>
    simp only [(txidDigestsOf_fields b).1, (txidDigestsOf_fields b).2.1,
      (txidDigestsOf_fields b).2.2, hcb, ite_true, SignableInput.hashType,
      Transparent.SighashType.encode, hacp, hsingle, hnone, hi, base_beq] <;>
    (try by_cases hio : i.val < b.vout.length) <;>
    (try have hio' : b.vout.length ≤ i.val := by omega) <;>
    simp only [hasher_pure, pure_bind, writeAll_absorbed, unwrap_pure, finalize_absorbed,
      OutPoint.write_absorbed, script_eq _ _ hsb, Verifier.Script.write_absorbed _ _ _ hsb,
      toLeBytes_i64, toLeBytes_u32, amounts_absorbed', scripts_absorbed _ _ _ hc.scriptLength,
      amounts_spec b hc, scripts_spec b hc, List.nil_append, Bool.not_true, Bool.not_false,
      some_eq_pure, hvin, hon, hpn, hsn, hio, hos,
      List.getElem?_eq_getElem, ite_true, ite_false] <;>
    simp only [sigPreimage, Spec.prevoutsSigDigest, Spec.amountsSigDigest,
      Spec.scriptPubKeysSigDigest, Spec.sequenceSigDigest, Spec.outputsSigDigest,
      Spec.txinSigDigest, Spec.SignableInput.hashType, Transparent.Bundle.txinToSpec,
      Spec.OutPoint.encode, Spec.TxOut.encode, List.getElem?_map, List.getElem?_eq_getElem,
      some_eq_pure, Option.map_none, List.getElem?_eq_none, *, ite_true, ite_false,
      Bool.false_eq_true, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.nil_append,
      List.cons_append, List.append_nil] <;>
    rfl

/-- Zakura's `transparent_sig_digest` gives §S.2's transparent signature digest. -/
theorem transparentSigDigest_eq (b : Transparent.Bundle) (hne : b.vin ≠ [] ∨ b.vout ≠ [])
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE)
    (hc' : ContextFitsIfRead b) (input : SignableInput) (sinput : Spec.SignableInput b.toSpec)
    (hr : InputRel b input sinput) :
    transparentSigDigest (some (b, txidDigestsOf b)) input =
      some (Spec.transparentSigDigest blake2b256 sinput).toList := by
  have hvin : b.toSpec.vin = [] ↔ b.vin = [] := by simp [Transparent.Bundle.toSpec]
  by_cases hcb : (b.isCoinbase || b.vin.isEmpty) = true
  · have hcb' : b.toSpec.IsCoinbase ∨ b.toSpec.vin = [] := by
      simpa [isCoinbase_toSpec, hvin, List.isEmpty_iff] using hcb
    simp only [transparentSigDigest, hcb, ite_true, Spec.transparentSigDigest, hcb']
    exact hashTransparentTxidData_some b hne
  · have hcb' : ¬(b.toSpec.IsCoinbase ∨ b.toSpec.vin = []) := by
      simpa [isCoinbase_toSpec, hvin, List.isEmpty_iff] using hcb
    have hc := hc' (by simpa using hcb)
    rw [Spec.transparentSigDigest, ite_eq_right hcb']
    rcases hr with _ | ⟨input, ht, i, hh, hi, hv, hs⟩
    · exact transparentSigDigest_shielded b hc hcb
    · exact transparentSigDigest_transparent b hk hc hcb input ht i hh hi hv hs

/-- Zakura's `signature_hash` gives the specification's signature digest, versions 5 and 6. -/
theorem signatureHash_eq (tx : TransactionData) (h : WellFormed tx) (b : Transparent.Bundle)
    (hb : tx.transparentBundle = some b) (hc : ContextFitsIfRead b) (input : SignableInput)
    (sinput : Spec.SignableInput b.toSpec) (hr : InputRel b input sinput) :
    signatureHash tx input (zip244DigestsOf tx) =
      some (Spec.signatureDigest blake2b256 (tx.toSpec.version blake2b256) tx.consensusBranchId
        (Spec.headerDigest blake2b256 tx.toSpec.header)
        (Spec.saplingDigest blake2b256 tx.toSpec.format tx.toSpec.sapling)
        (tx.toSpec.orchardDigest blake2b256) sinput).toList := by
  have hts := transparentSigDigest_eq b (h.transparentNonempty b hb) (h.outputScripts b hb) hc
    input sinput hr
  have hs := saplingSlot tx
  rcases h.version with hv | hv
  · have ho := orchardSlot tx Spec.orchardV5 false
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [signatureHash, v5SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, Option.map_some, Option.isSome_some, zipOption, guard, ite_true]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHash_eq _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq
      hashBundleTxidEmpty_orchard_v5, hs, ho]
    simp [Spec.signatureDigest, Spec.Transaction.version, Spec.Transaction.orchardDigest,
      TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]
  · have ho := orchardSlot tx Spec.orchardV6 true
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [signatureHash, v6SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, ite_true, Option.map_some, Option.isSome_some, zipOption, guard]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHashV6_eq _ _ _ _ _ _ _ _ _
      hashSaplingTxidEmpty_eq hashBundleTxidEmpty_orchard_v6 hashBundleTxidEmpty_ironwood_v6, hs,
      ho, ironwoodSlot]
    simp [Spec.signatureDigest, Spec.Transaction.version, Spec.Transaction.orchardDigest,
      TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]

/-- For a well-formed transaction, Zakura's `TxIdDigester` computes the specification's digests
    (`zip244DigestsOf`: ZIP 244's, with ZIP 229's in version 6), the ones `signatureHash_eq`
    hashes. -/
theorem txIdDigests_zip244 (tx : TransactionData) (h : WellFormed tx) :
    TransactionData.txIdDigests tx = some (zip244DigestsOf tx) := by
  rw [txIdDigests_eq' tx h, Verifier.txIdDigests_eq tx h]
  rfl

/-- Zakura's `outputs_hash` is ZIP 143's `hashOutputs`, when the scripts fit in a
    `compactSize`. -/
theorem outputsHash_eq (vout : List Transparent.TxOut)
    (hk : ∀ o ∈ vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    outputsHash vout = some (blake2b256 (personal "ZcashOutputsHash")
      (vout.flatMap fun o => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList := by
  simp only [outputsHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_vec vout [] (fun o => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)
    (fun (a : Transparent.TxOut) r => unwrap (TxOut.write a r))
    (fun o ho _ => by simp [txOut_eq _ _ (hk o ho), TxOut.write_vec _ _ (hk o ho), unwrap_ok])]
  simp [hashWith_eq]

/-- Zakura's `single_output_hash` is ZIP 143's `hashOutputs` for `SIGHASH_SINGLE`. -/
theorem singleOutputHash_eq (o : Transparent.TxOut)
    (hk : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    singleOutputHash o = some (blake2b256 (personal "ZcashOutputsHash")
      (Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList := by
  simp [singleOutputHash, txOut_eq _ _ hk, TxOut.write_vec _ _ hk, unwrap_ok, hashWith_eq]

/-- `update_hash!` absorbs the digest when its condition holds and 32 zero bytes otherwise;
    the digest is computed, and must succeed, only when the condition holds. -/
theorem updateHashLazy_absorbed (p : Bytes 16) (x : List Byte) (c : Bool)
    (v : Unit → Option Blake2bHash) (V : Blake2bHash) (hv : c = true → v () = pure V) :
    updateHashLazy (absorbed p x).state c v =
      pure (absorbed p (x ++ if c then V else List.replicate 32 0)).state := by
  cases c
  · simp [updateHashLazy, update_absorbed]
  · simp [updateHashLazy, hv rfl, update_absorbed]

/-- The `hashJoinSplits` step of Zakura's `v4_signature_hash` absorbs ZIP 143's field. -/
theorem sproutStep (tx : TransactionData) (t : Spec.Transparent) (p : Bytes 16) (x : List Byte) :
    updateHashLazy (absorbed p x).state (!isNoneOr tx.sproutBundle (·.joinsplits.isEmpty))
      (fun _ => do
        let bundle ← tx.sproutBundle
        joinsplitsHash bundle.joinsplits bundle.joinsplitPubkey) =
      pure (absorbed p (x ++ Spec.digestOrZero (!(tx.toLegacySpec t).joinSplits.isEmpty)
        (blake2b256 (personal "ZcashJSplitsHash")
          ((tx.toLegacySpec t).joinSplits.flatMap Spec.JoinSplit.encode ++
            (tx.toLegacySpec t).joinSplitPubKey.toList)))).state := by
  cases hs : tx.sproutBundle with
  | none =>
    simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs,
      Spec.digestOrZero]
  | some s =>
    by_cases he : s.joinsplits = [] <;>
      simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs, he,
        Spec.digestOrZero, joinsplitsHash_eq, List.flatMap_map]

/-- The `hashShieldedSpends` step absorbs ZIP 243's field. -/
theorem spendsStep (tx : TransactionData) (t : Spec.Transparent) (p : Bytes 16) (x : List Byte) :
    updateHashLazy (absorbed p x).state (!isNoneOr tx.saplingBundle (·.shieldedSpends.isEmpty))
      (fun _ => do saplingSpendsHash (← tx.saplingBundle).shieldedSpends) =
      pure (absorbed p (x ++ Spec.digestOrZero (!(tx.toLegacySpec t).saplingSpends.isEmpty)
        (blake2b256 (personal "ZcashSSpendsHash")
          ((tx.toLegacySpec t).saplingSpends.flatMap Spec.SpendV4.encode)))).state := by
  cases hs : tx.saplingBundle with
  | none =>
    simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs,
      Spec.digestOrZero]
  | some s =>
    by_cases he : s.shieldedSpends = [] <;>
      simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs, he,
        Spec.digestOrZero, saplingSpendsHash_eq, List.flatMap_map, Spec.SpendV4.encode,
        Sapling.SpendDescription.toSpecV4]

/-- The `hashShieldedOutputs` step absorbs ZIP 243's field. -/
theorem outputsStep (tx : TransactionData) (t : Spec.Transparent) (p : Bytes 16)
    (x : List Byte) :
    updateHashLazy (absorbed p x).state (!isNoneOr tx.saplingBundle (·.shieldedOutputs.isEmpty))
      (fun _ => do saplingOutputsHash (← tx.saplingBundle).shieldedOutputs) =
      pure (absorbed p (x ++ Spec.digestOrZero (!(tx.toLegacySpec t).saplingOutputs.isEmpty)
        (blake2b256 (personal "ZcashSOutputHash")
          ((tx.toLegacySpec t).saplingOutputs.flatMap Spec.SaplingOutput.encode)))).state := by
  cases hs : tx.saplingBundle with
  | none =>
    simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs,
      Spec.digestOrZero]
  | some s =>
    by_cases he : s.shieldedOutputs = [] <;>
      simp [updateHashLazy, update_absorbed, isNoneOr, TransactionData.toLegacySpec, hs, he,
        Spec.digestOrZero, saplingOutputsHash_eq, List.flatMap_map, Spec.SaplingOutput.encode,
        Sapling.OutputDescription.toSpec]

/-- Zakura's `v4_signature_hash` gives ZIP 143's or ZIP 243's digest for a transparent input. -/
theorem v4SignatureHash_transparent (tx : TransactionData)
    (hv : tx.version = .v3 ∨ tx.version = .v4)
    (b : Transparent.Bundle) (hb : tx.transparentBundle = some b)
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE)
    (input : Transparent.SignableInput) (i : Fin b.toSpec.vin.length)
    (hi : input.index = i.val) (hval : input.value = b.authorization.inputAmounts.getD i 0)
    (hsc : input.scriptCode.code.length ≤ MAX_COMPACT_SIZE) :
    v4SignatureHash tx (.transparent input) = some (Spec.legacySignatureDigest blake2b256
      (tx.toLegacySpec b.toSpec)
      (.transparent input.hashType.byte i input.scriptCode.code)).toList := by
  have hPv : ∀ p x c, updateHashLazy (absorbed p x).state c (fun _ => prevoutHash b.vin) =
      pure (absorbed p (x ++ if c then (blake2b256 (personal "ZcashPrevoutHash")
        (b.toSpec.vin.flatMap (·.prevout.encode))).toList else List.replicate 32 0)).state :=
    fun p x c => updateHashLazy_absorbed p x c _ _ fun _ => by
      rw [prevoutHash_eq]
      simpa [List.flatMap_map, Spec.OutPoint.encode] using
        congrArg (fun l => some (blake2b256 (personal "ZcashPrevoutHash")
          (List.flatMap Spec.OutPoint.encode l)).toList) (toSpec_prevouts b).symm
  have hSv : ∀ p x c, updateHashLazy (absorbed p x).state c (fun _ => sequenceHash b.vin) =
      pure (absorbed p (x ++ if c then (blake2b256 (personal "ZcashSequencHash")
        (b.toSpec.vin.flatMap (Spec.u32 ·.nSequence))).toList else List.replicate 32 0)).state :=
    fun p x c => updateHashLazy_absorbed p x c _ _ fun _ => by
      rw [sequenceHash_eq]
      simpa [List.flatMap_map] using
        congrArg (fun l => some (blake2b256 (personal "ZcashSequencHash")
          (List.flatMap Spec.u32 l)).toList) (toSpec_sequences b).symm
  have hOv : outputsHash b.vout = pure (blake2b256 (personal "ZcashOutputsHash")
      (b.toSpec.vout.flatMap Spec.TxOut.encode)).toList := by
    rw [outputsHash_eq _ hk]; simp [Transparent.Bundle.toSpec, List.flatMap_map, Spec.TxOut.encode]
  have hlen : b.toSpec.vin.length = b.vin.length := by simp [Transparent.Bundle.toSpec]
  have hi' : i.val < b.vin.length := by have := i.isLt; omega
  have hvin : b.vin[input.index]? = pure b.vin[i.val] := by
    rw [hi]; exact List.getElem?_eq_getElem hi'
  have htxin : b.toSpec.vin[i] = b.txinToSpec i b.vin[i.val] := by
    show (b.vin.mapIdx b.txinToSpec)[i.val]'(by simpa using hi') = _
    exact List.getElem_mapIdx
  have hout : ∀ (h : i.val < b.vout.length), b.vout[i.val]? = pure b.vout[i.val] :=
    fun h => List.getElem?_eq_getElem h
  have hso : ∀ (h : i.val < b.vout.length), singleOutputHash b.vout[i.val] =
      pure (blake2b256 (personal "ZcashOutputsHash")
        (Spec.i64 b.vout[i.val].value ++ Spec.script b.vout[i.val].scriptPubkey.code)).toList :=
    fun h => singleOutputHash_eq _ (hk _ (List.getElem_mem _))
  have hvout : b.toSpec.vout = b.vout.map fun o => ⟨o.value, o.scriptPubkey.code⟩ := rfl
  have hpers : branchPersonalization (Spec.ascii "ZcashSigHash" 12) tx.consensusBranchId =
      ⟨(Spec.ascii "ZcashSigHash" 12).toList ++ Spec.u32 tx.consensusBranchId,
        by simp [Spec.ascii, Spec.u32, Spec.I2LEOSP]⟩ := rfl
  have hsp := sproutStep tx b.toSpec
  have hss := spendsStep tx b.toSpec
  have hso' := outputsStep tx b.toSpec
  unfold v4SignatureHash
  dsimp only [SignableInput.hashType, Transparent.SighashType.encode]
  rcases hv with hv | hv <;>
    simp only [hv, TxVersion.hasOverwinter, Bool.not_true, Bool.false_eq_true, ite_false,
      hashLength?_32_pure, personal?_16_pure, pure_bind, toState_absorbed, update_absorbed,
      hb, Option.map_some, Option.getD_some, hPv, hSv, hOv, hsp, hss, hso', hvin,
      OutPoint.write_vec, unwrap_pure, script_eq _ _ hsc, Script.write_vec _ _ hsc,
      finalize_state_absorbed, TxVersion.hasSapling] <;>
    simp only [Transparent.SIGHASH_ANYONECANPAY, Transparent.SIGHASH_MASK,
      Transparent.SIGHASH_SINGLE, Transparent.SIGHASH_NONE, Spec.legacySignatureDigest,
      TransactionData.toLegacySpec, hv, Spec.LegacyInput.hashType, htxin,
      Transparent.Bundle.txinToSpec, bne, Bool.not_not] <;>
    rcases Bool.eq_false_or_eq_true (input.hashType.byte &&& 128 == 0) with hA | hA <;>
    rcases Bool.eq_false_or_eq_true (input.hashType.byte &&& 31 == 3) with hSg | hSg <;>
    rcases Bool.eq_false_or_eq_true (input.hashType.byte &&& 31 == 2) with hN | hN <;>
    (try by_cases hio : i.val < b.vout.length) <;>
    (try have hio' : b.vout.length ≤ i.val := by omega) <;>
    simp only [ite_true, ite_false, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, *] <;>
    simp only [pure_bind, toLeBytes_u32, toLeBytes_i64, Spec.digestOrZero, List.getElem?_map,
      List.getElem?_eq_none, Option.map_none, ite_true, ite_false, List.append_assoc,
      List.nil_append, Spec.TxOut.encode, Spec.OutPoint.encode, Bool.false_eq_true, some_eq_pure,
      *] <;>
    congr!

/-- Zakura's `v4_signature_hash` gives the digest a JoinSplit, Spend or binding signature signs. -/
theorem v4SignatureHash_shielded (tx : TransactionData)
    (hv : tx.version = .v3 ∨ tx.version = .v4)
    (hk : ∀ b, tx.transparentBundle = some b →
      ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    v4SignatureHash tx .shielded = some (Spec.legacySignatureDigest blake2b256
      (tx.toLegacySpec tx.transparentSpec) .shielded).toList := by
  have hk' : ∀ o ∈ (tx.transparentBundle.map (·.vout)).getD [],
      o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := by
    cases hb : tx.transparentBundle with
    | none => simp
    | some b => simpa using hk b hb
  have hPv : ∀ p x c, updateHashLazy (absorbed p x).state c
      (fun _ => prevoutHash ((tx.transparentBundle.map (·.vin)).getD [])) =
      pure (absorbed p (x ++ if c then (blake2b256 (personal "ZcashPrevoutHash")
        (tx.transparentSpec.vin.flatMap (·.prevout.encode))).toList
        else List.replicate 32 0)).state :=
    fun p x c => updateHashLazy_absorbed p x c _ _ fun _ => by
      rw [prevoutHash_eq]
      cases hb : tx.transparentBundle with
      | none => simp [TransactionData.transparentSpec, hb]
      | some b =>
        simpa [TransactionData.transparentSpec, hb, List.flatMap_map, Spec.OutPoint.encode] using
          congrArg (fun l => some (blake2b256 (personal "ZcashPrevoutHash")
            (List.flatMap Spec.OutPoint.encode l)).toList) (toSpec_prevouts b).symm
  have hSv : ∀ p x c, updateHashLazy (absorbed p x).state c
      (fun _ => sequenceHash ((tx.transparentBundle.map (·.vin)).getD [])) =
      pure (absorbed p (x ++ if c then (blake2b256 (personal "ZcashSequencHash")
        (tx.transparentSpec.vin.flatMap (Spec.u32 ·.nSequence))).toList
        else List.replicate 32 0)).state :=
    fun p x c => updateHashLazy_absorbed p x c _ _ fun _ => by
      rw [sequenceHash_eq]
      cases hb : tx.transparentBundle with
      | none => simp [TransactionData.transparentSpec, hb]
      | some b =>
        simpa [TransactionData.transparentSpec, hb, List.flatMap_map] using
          congrArg (fun l => some (blake2b256 (personal "ZcashSequencHash")
            (List.flatMap Spec.u32 l)).toList) (toSpec_sequences b).symm
  have hOv : outputsHash ((tx.transparentBundle.map (·.vout)).getD []) =
      pure (blake2b256 (personal "ZcashOutputsHash")
        (tx.transparentSpec.vout.flatMap Spec.TxOut.encode)).toList := by
    rw [outputsHash_eq _ hk']
    cases hb : tx.transparentBundle <;>
      simp [TransactionData.transparentSpec, hb, Transparent.Bundle.toSpec, List.flatMap_map,
        Spec.TxOut.encode]
  have hpers : branchPersonalization (Spec.ascii "ZcashSigHash" 12) tx.consensusBranchId =
      ⟨(Spec.ascii "ZcashSigHash" 12).toList ++ Spec.u32 tx.consensusBranchId,
        by simp [Spec.ascii, Spec.u32, Spec.I2LEOSP]⟩ := rfl
  have hsp := sproutStep tx tx.transparentSpec
  have hss := spendsStep tx tx.transparentSpec
  have hso' := outputsStep tx tx.transparentSpec
  have hall := all_flags_v4
  unfold v4SignatureHash
  dsimp only [SignableInput.hashType]
  simp only [hall.1, hall.2.1, hall.2.2, Bool.and_self, ite_true]
  rcases hv with hv | hv <;>
    simp only [hv, TxVersion.hasOverwinter, TxVersion.hasSapling, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] <;>
    simp only [hashLength?_32_pure, personal?_16_pure, pure_bind, toState_absorbed,
      update_absorbed, finalize_state_absorbed, hPv, hSv, hOv, hsp, hss, hso', ite_true] <;>
    simp only [Spec.legacySignatureDigest, TransactionData.toLegacySpec, hv,
      Spec.LegacyInput.hashType, Transparent.SIGHASH_ALL, toLeBytes_u32, toLeBytes_i64,
      Spec.digestOrZero, hpers, List.append_assoc, List.nil_append, List.append_nil,
      Bool.false_eq_true, ite_true, ite_false, some_eq_pure] <;>
    congr!

/-- Without a transparent bundle, Zakura's `signature_hash` gives the shielded signature digest,
    for a transparent input too. -/
theorem signatureHash_noTransparent (tx : TransactionData) (h : WellFormed tx)
    (hb : tx.transparentBundle = none) (input : SignableInput) :
    signatureHash tx input (zip244DigestsOf tx) =
      some (tx.toSpec.signatureDigest blake2b256 .shielded).toList := by
  have hts : transparentSigDigest none input =
      some (Spec.transparentSigDigest blake2b256 (t := tx.toSpec.transparent)
        .shielded).toList := by
    simp [transparentSigDigest, hashTransparentTxidData_none, Spec.transparentSigDigest,
      TransactionData.toSpec, hb]
  have hs := saplingSlot tx
  rcases h.version with hv | hv
  · have ho := orchardSlot tx Spec.orchardV5 false
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [signatureHash, v5SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, Option.map_none, Option.isSome_none, zipOption, guard, ite_true]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHash_eq _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq
      hashBundleTxidEmpty_orchard_v5, hs, ho]
    simp [Spec.Transaction.signatureDigest, Spec.signatureDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]
  · have ho := orchardSlot tx Spec.orchardV6 true
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [signatureHash, v6SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, ite_true, Option.map_none, Option.isSome_none, zipOption, guard]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHashV6_eq _ _ _ _ _ _ _ _ _
      hashSaplingTxidEmpty_eq hashBundleTxidEmpty_orchard_v6 hashBundleTxidEmpty_ironwood_v6, hs,
      ho, ironwoodSlot]
    simp [Spec.Transaction.signatureDigest, Spec.signatureDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]

/-- Zakura writes a script of any length as the specification encodes it, where librustzcash
    panics above `MAX_COMPACT_SIZE` (`script_write_long`). -/
theorem script_write_absorbed (s : Transparent.Script) (p : Bytes 16) (x : List Byte)
    (hs : s.code.length < 2 ^ 64) :
    Script.write s (absorbed p x) = .ok (absorbed p (x ++ Spec.script s.code)) := by
  simp only [Script.write, Vector.write, compactSize_absorbed p x _ hs, bind, Except.bind]
  rw [foldlM_absorbed s.code p _ (fun e => [e]) _ fun e _ y => classWrite_absorbed p y [e]]
  simp [Spec.script]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Zakura.txid_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms txid_eq

/--
info: 'ZcashSighash.Verifier.Zakura.authCommitment_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms authCommitment_eq

/--
info: 'ZcashSighash.Verifier.Zakura.signatureHash_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signatureHash_eq

/--
info: 'ZcashSighash.Verifier.Zakura.v4SignatureHash_transparent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v4SignatureHash_transparent

/--
info: 'ZcashSighash.Verifier.Zakura.v4SignatureHash_shielded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v4SignatureHash_shielded

end ZcashSighash.Verifier.Zakura
