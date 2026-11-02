/-
The transcribed `v4_signature_hash` computes ZIP 143's and ZIP 243's signature digests, with
BLAKE2b-256, for every version 3 and 4 transaction whose scripts fit in a `compactSize`.
-/
module

public import ZcashSighash.Proofs.Verifier
public import ZcashSighash.Verifier.SighashV4

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)
/-- `Params::hash` with a personalization is the specification's BLAKE2b-256. Version 4 hashes
    each component in one call, over a byte buffer, where version 5 streams into a state. -/
theorem hashWith_eq (p : Bytes 16) (data : List Byte) :
    hashWith p data = some (blake2b256 p data).toList := by
  simp [hashWith, Blake2b.Params.new, Blake2b.Params.hashLength?, Blake2b.Params.personal?,
    Blake2b.outBytes, Blake2b.personalBytes, blake2b256]

/-- Writing to a `Vec<u8>` succeeds and appends. -/
theorem vec_write (v b : List Byte) : Write.writeAll (v : VecU8) b = .ok (v ++ b) := rfl

/-- A loop that appends `f a` to a buffer for each `a`, through writes that cannot fail. -/
theorem forIn_vec {α : Type} (l : List α) (x : List Byte) (f : α → List Byte)
    (body : α → VecU8 → Option VecU8)
    (hb : ∀ a ∈ l, ∀ y, body a y = some (y ++ f a)) :
    forIn l (x : VecU8) (fun a r => (body a r).bind fun r => some (ForInStep.yield r)) =
      some (x ++ l.flatMap f) := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons, hb a List.mem_cons_self, Option.bind_eq_bind, Option.bind_some]
    simpa [List.append_assoc] using ih (x ++ f a) (fun a h => hb a (List.mem_cons_of_mem _ h))

/-- An outpoint is written to a buffer as its field encoding. -/
theorem OutPoint.write_vec (o : Transparent.OutPoint) (v : List Byte) :
    o.write (v : VecU8) = .ok (v ++ (o.hash.toList ++ Spec.u32 o.n)) := by
  simp [Transparent.OutPoint.write, vec_write, bind, Except.bind, toLeBytes_u32]

/-- `CompactSize::write_unbounded` appends the specification's `compactSize` encoding to a
    buffer. -/
theorem writeUnbounded_vec (x : List Byte) (v : BitVec 64) :
    CompactSize.writeUnbounded (x : VecU8) v = .ok (x ++ Spec.compactSize v) := by
  unfold CompactSize.writeUnbounded Spec.compactSize
  dsimp only
  split_ifs <;>
    simp [vec_write, toLeBytes, Spec.I2LEOSP, List.range_succ, bind, Except.bind] <;>
    rw [Nat.mod_eq_of_lt (by omega)] <;> simp [BitVec.ofNat_toNat]

/-- A fold that appends `f a` to a buffer for each `a` appends their concatenation. -/
theorem foldlM_vec {α : Type} (l : List α) (x : List Byte) (f : α → List Byte)
    (func : VecU8 → α → IoResult VecU8) (hf : ∀ a ∈ l, ∀ y, func y a = .ok (y ++ f a)) :
    l.foldlM func (x : VecU8) = .ok (x ++ l.flatMap f) := by
  induction l generalizing x with
  | nil => simp [pure, Except.pure]
  | cons a l ih =>
    simp only [List.foldlM_cons, hf a List.mem_cons_self, bind, Except.bind]
    simpa [List.append_assoc] using ih (x ++ f a) (fun a h => hf a (List.mem_cons_of_mem _ h))

/-- A script no longer than `MAX_COMPACT_SIZE` is written to a buffer as its `script` field. -/
theorem Script.write_vec (s : Transparent.Script) (v : List Byte)
    (hs : s.code.length ≤ MAX_COMPACT_SIZE) :
    s.write (v : VecU8) = .ok (v ++ Spec.script s.code) := by
  simp only [Transparent.Script.write, Vector.write, CompactSize.write, Nat.not_lt.mpr hs,
    ite_false, writeUnbounded_vec, bind, Except.bind]
  rw [foldlM_vec s.code _ (fun e => [e]) _ fun e _ y => vec_write y [e]]
  simp [Spec.script]

/-- An output whose script fits in a `compactSize` is written to a buffer as its field
    encoding. -/
theorem TxOut.write_vec (o : Transparent.TxOut) (v : List Byte)
    (hs : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    o.write (v : VecU8) = .ok (v ++ (Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)) := by
  simp [Transparent.TxOut.write, vec_write, bind, Except.bind, toLeBytes_i64,
    Script.write_vec _ _ hs]

/-- A JoinSplit description, as the specification's. -/
def Sprout.JsDescription.toSpec (js : Sprout.JsDescription) : Spec.JoinSplit :=
  ⟨js.vpubOld, js.vpubNew, js.anchor, js.nullifiers, js.commitments, js.ephemeralKey,
    js.randomSeed, js.macs, (match js.proof with | .groth p => p.toList | .phgr p => p.toList),
    js.ciphertexts⟩

/-- `JsDescription::write` appends the specification's JoinSplit encoding, for either proof
    system. -/
theorem JsDescription.write_vec (js : Sprout.JsDescription) (v : List Byte) :
    js.write (v : VecU8) = .ok (v ++ js.toSpec.encode) := by
  cases hp : js.proof <;>
    simp [Sprout.JsDescription.write, Sprout.JsDescription.toSpec, Spec.JoinSplit.encode, hp,
      vec_write, bind, Except.bind, toLeBytes_i64]

/-- `write_output_v4` appends the Output's version 4 encoding. -/
theorem writeOutputV4_vec (o : Sapling.OutputDescription) (v : List Byte) :
    writeOutputV4 (v : VecU8) o = .ok (v ++ o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++
      o.encCiphertext.toList ++ o.outCiphertext.toList ++ o.zkproof.toList) := by
  simp [writeOutputV4, vec_write, bind, Except.bind]

/-- Appending `f a` for each `a` appends their concatenation. -/
theorem foldl_append {α : Type} (l : List α) (x : List Byte) (f : α → List Byte) :
    l.foldl (fun s a => s ++ f a) x = x ++ l.flatMap f := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, List.append_assoc]

/-- `prevout_hash` is ZIP 143's `hashPrevouts` digest, before the `ANYONECANPAY` choice. -/
theorem prevoutHash_eq (vin : List Transparent.TxIn) :
    prevoutHash vin = some (blake2b256 (personal "ZcashPrevoutHash")
      (vin.flatMap fun i => i.prevout.hash.toList ++ Spec.u32 i.prevout.n)).toList := by
  simp only [prevoutHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_vec vin [] (fun i => i.prevout.hash.toList ++ Spec.u32 i.prevout.n)
    (fun (a : Transparent.TxIn) r => unwrap (a.prevout.write r))
    (fun _ _ _ => by simp [OutPoint.write_vec, unwrap_ok])]
  simp [hashWith_eq]

/-- `sequence_hash` is ZIP 143's `hashSequence` digest, before the hash-type choice. -/
theorem sequenceHash_eq (vin : List Transparent.TxIn) :
    sequenceHash vin = some (blake2b256 (personal "ZcashSequencHash")
      (vin.flatMap fun i => Spec.u32 i.sequence)).toList := by
  simp only [sequenceHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_yield _ _ _ (fun (a : Transparent.TxIn) (s : VecU8) => s ++ toLeBytes 4 a.sequence)
    (fun _ _ _ => rfl), foldl_append]
  simp [hashWith_eq, toLeBytes_u32]

/-- `outputs_hash` is ZIP 143's `hashOutputs` over all outputs, when their scripts fit in a
    `compactSize`. -/
theorem outputsHash_eq (vout : List Transparent.TxOut)
    (hk : ∀ o ∈ vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    outputsHash vout = some (blake2b256 (personal "ZcashOutputsHash")
      (vout.flatMap fun o => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList := by
  simp only [outputsHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_vec vout [] (fun o => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)
    (fun (a : Transparent.TxOut) r => unwrap (a.write r))
    (fun o ho _ => by simp [TxOut.write_vec _ _ (hk o ho), unwrap_ok])]
  simp [hashWith_eq]

/-- `single_output_hash` is ZIP 143's `hashOutputs` for `SIGHASH_SINGLE`. -/
theorem singleOutputHash_eq (o : Transparent.TxOut)
    (hk : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    singleOutputHash o = some (blake2b256 (personal "ZcashOutputsHash")
      (Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList := by
  simp [singleOutputHash, TxOut.write_vec _ _ hk, unwrap_ok, hashWith_eq]

/-- `joinsplits_hash` is ZIP 143's `hashJoinSplits` digest. -/
theorem joinsplitsHash_eq (js : List Sprout.JsDescription) (pk : Bytes 32) :
    joinsplitsHash js pk = some (blake2b256 (personal "ZcashJSplitsHash")
      (js.flatMap (·.toSpec.encode) ++ pk.toList)).toList := by
  simp only [joinsplitsHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_vec js [] (fun j => j.toSpec.encode)
    (fun (a : Sprout.JsDescription) r => unwrap (a.write r))
    (fun _ _ _ => by simp [JsDescription.write_vec, unwrap_ok])]
  simp [hashWith_eq]

/-- `sapling_spends_hash` is ZIP 243's `hashShieldedSpends` digest, each spend with its own
    anchor. -/
theorem saplingSpendsHash_eq (spends : List Sapling.SpendDescription) :
    saplingSpendsHash spends = some (blake2b256 (personal "ZcashSSpendsHash")
      (spends.flatMap fun s => s.cv.toList ++ s.anchor.toList ++ s.nullifier.toList ++
        s.rk.toList ++ s.zkproof.toList)).toList := by
  simp only [saplingSpendsHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_yield _ _ _ (fun (a : Sapling.SpendDescription) (s : VecU8) =>
    s ++ (a.cv.toList ++ a.anchor.toList ++ a.nullifier.toList ++ a.rk.toList ++
      a.zkproof.toList)) (fun _ _ _ => by simp), foldl_append]
  simp [hashWith_eq]

/-- `sapling_outputs_hash` is ZIP 243's `hashShieldedOutputs` digest. -/
theorem saplingOutputsHash_eq (outputs : List Sapling.OutputDescription) :
    saplingOutputsHash outputs = some (blake2b256 (personal "ZcashSOutputHash")
      (outputs.flatMap fun o => o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++
        o.encCiphertext.toList ++ o.outCiphertext.toList ++ o.zkproof.toList)).toList := by
  simp only [saplingOutputsHash, Option.pure_def, Option.bind_eq_bind]
  rw [forIn_vec outputs [] (fun o => o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++
      o.encCiphertext.toList ++ o.outCiphertext.toList ++ o.zkproof.toList)
    (fun (a : Sapling.OutputDescription) r => unwrap (writeOutputV4 r a))
    (fun _ _ _ => by simp [writeOutputV4_vec, unwrap_ok, List.append_assoc])]
  simp [hashWith_eq]

/-- A version 4 Sapling spend, as the specification's. -/
def Sapling.SpendDescription.toSpecV4 (s : Sapling.SpendDescription) : Spec.SpendV4 :=
  ⟨s.cv, s.anchor, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩

/-- A Sapling output, as the specification's. -/
def Sapling.OutputDescription.toSpec (o : Sapling.OutputDescription) : Spec.SaplingOutput :=
  ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, o.zkproof⟩

/-- A version 3 or 4 transaction's data, as the specification's, with the transparent part
    `t`. -/
def TransactionData.toLegacySpec (tx : TransactionData) (t : Spec.Transparent) :
    Spec.LegacyTransaction :=
  ⟨match tx.version with | .v3 => .v3 | _ => .v4,
    ⟨tx.version.header, tx.version.versionGroupId, tx.consensusBranchId, tx.lockTime,
      tx.expiryHeight⟩, t,
    (tx.sproutBundle.map (·.joinsplits.map Sprout.JsDescription.toSpec)).getD [],
    (tx.sproutBundle.map (·.joinsplitPubkey)).getD (List.Vector.replicate 32 0),
    (tx.saplingBundle.map (·.shieldedSpends.map Sapling.SpendDescription.toSpecV4)).getD [],
    (tx.saplingBundle.map (·.shieldedOutputs.map Sapling.OutputDescription.toSpec)).getD [],
    tx.saplingValueBalance⟩

/-- `zip143_digests` computes each ZIP 143 and ZIP 243 component digest, a JoinSplit or
    Sapling one only when its list is not empty, when the outputs' scripts fit in a
    `compactSize`. -/
theorem zip143Digests_eq (tx : TransactionData)
    (hk : ∀ b, tx.transparentBundle = some b →
      ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    zip143Digests tx = some
      ⟨⟨(blake2b256 (personal "ZcashPrevoutHash")
            (((tx.transparentBundle.map (·.vin)).getD []).flatMap fun i =>
              i.prevout.hash.toList ++ Spec.u32 i.prevout.n)).toList,
          (blake2b256 (personal "ZcashSequencHash")
            (((tx.transparentBundle.map (·.vin)).getD []).flatMap fun i =>
              Spec.u32 i.sequence)).toList,
          (blake2b256 (personal "ZcashOutputsHash")
            (((tx.transparentBundle.map (·.vout)).getD []).flatMap fun o =>
              Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList⟩,
        (tx.sproutBundle.filter (!·.joinsplits.isEmpty)).map fun b =>
          (blake2b256 (personal "ZcashJSplitsHash")
            (b.joinsplits.flatMap (·.toSpec.encode) ++ b.joinsplitPubkey.toList)).toList,
        (tx.saplingBundle.filter (!·.shieldedSpends.isEmpty)).map fun b =>
          (blake2b256 (personal "ZcashSSpendsHash") (b.shieldedSpends.flatMap fun s =>
            s.cv.toList ++ s.anchor.toList ++ s.nullifier.toList ++ s.rk.toList ++
              s.zkproof.toList)).toList,
        (tx.saplingBundle.filter (!·.shieldedOutputs.isEmpty)).map fun b =>
          (blake2b256 (personal "ZcashSOutputHash") (b.shieldedOutputs.flatMap fun o =>
            o.cv.toList ++ o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList ++
              o.outCiphertext.toList ++ o.zkproof.toList)).toList⟩ := by
  have hk' : ∀ o ∈ (tx.transparentBundle.map (·.vout)).getD [],
      o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := by
    cases hb : tx.transparentBundle with
    | none => simp
    | some b => simpa using hk b hb
  unfold zip143Digests
  cases tx.sproutBundle.filter (!·.joinsplits.isEmpty) <;>
    cases tx.saplingBundle.filter (!·.shieldedSpends.isEmpty) <;>
    cases tx.saplingBundle.filter (!·.shieldedOutputs.isEmpty) <;>
    simp [joinsplitsHash_eq, saplingSpendsHash_eq, saplingOutputsHash_eq, prevoutHash_eq,
      sequenceHash_eq, outputsHash_eq _ hk']

/-- `Params::new().hash_length(32)` does not panic. -/
theorem hashLength?_32 :
    Blake2b.Params.new.hashLength? 32 = some ⟨32, List.replicate 16 0⟩ := rfl

/-- A 16-byte personalization does not panic, and gives the parameters of `absorbed p []`. -/
theorem personal?_16 (p : Bytes 16) :
    (⟨32, List.replicate 16 0⟩ : Blake2b.Params).personal? (p.toList.map (·.toNat)) =
      some (absorbed p []).state.params := by
  simp [Blake2b.Params.personal?, Blake2b.personalBytes, absorbed]

/-- `to_state` on those parameters is the empty personalized state. -/
theorem toState_absorbed (p : Bytes 16) :
    (absorbed p []).state.params.toState = (absorbed p []).state := rfl

/-- `update_hash!` absorbs the digest when its condition holds, and 32 zero bytes otherwise:
    ZIP 143's "`uint256` of `0x0000......0000`". -/
theorem updateHash_absorbed (p : Bytes 16) (x : List Byte) (c : Bool) (v : Blake2bHash) :
    updateHash (absorbed p x).state c v =
      (absorbed p (x ++ if c then v else List.replicate 32 0)).state := by
  cases c <;> simp [updateHash, update_absorbed]

/-- Binding `some a` applies the continuation to `a`. -/
theorem some_bind' {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

/-- `v4_signature_hash` gives ZIP 143's or ZIP 243's digest for the transparent input at `i`:
    with any hash-type byte, its `scriptCode`, and the value the authorizing context gives. The
    transaction's scripts must fit in a `compactSize`. -/
theorem v4SignatureHash_transparent (tx : TransactionData)
    (hv : tx.version = .v3 ∨ tx.version = .v4)
    (b : Transparent.Bundle) (hb : tx.transparentBundle = some b)
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE)
    (input : Transparent.SignableInput) (i : Fin b.toSpec.vin.length)
    (hi : input.index = i.val) (hval : input.value = b.authorization.inputAmounts.getD i 0)
    (hsc : input.scriptCode.code.length ≤ MAX_COMPACT_SIZE) (d : Zip143Digests)
    (hd : zip143Digests tx = some d) :
    v4SignatureHash tx (.transparent input) d = some (Spec.legacySignatureDigest blake2b256
      (tx.toLegacySpec b.toSpec)
      (.transparent input.hashType.byte i input.scriptCode.code)).toList := by
  have hk' : ∀ (bb : Transparent.Bundle), tx.transparentBundle = some bb →
      ∀ o ∈ bb.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE := by
    intro bb hbb; rw [hb] at hbb; cases hbb; exact hk
  rw [zip143Digests_eq tx hk'] at hd
  have hd' := (Option.some.inj hd).symm
  have hP : d.transparent.prevoutsDigest = (blake2b256 (personal "ZcashPrevoutHash")
      (b.toSpec.vin.flatMap (·.prevout.encode))).toList := by
    rw [hd']
    simpa [hb, List.flatMap_map, Spec.OutPoint.encode] using
      congrArg (fun l => (blake2b256 (personal "ZcashPrevoutHash")
        (List.flatMap Spec.OutPoint.encode l)).toList) (toSpec_prevouts b).symm
  have hS : d.transparent.sequenceDigest = (blake2b256 (personal "ZcashSequencHash")
      (b.toSpec.vin.flatMap (Spec.u32 ·.nSequence))).toList := by
    rw [hd']
    simpa [hb, List.flatMap_map] using
      congrArg (fun l => (blake2b256 (personal "ZcashSequencHash")
        (List.flatMap Spec.u32 l)).toList) (toSpec_sequences b).symm
  have hO : d.transparent.outputsDigest = (blake2b256 (personal "ZcashOutputsHash")
      (b.toSpec.vout.flatMap Spec.TxOut.encode)).toList := by
    rw [hd']; simp [hb, Transparent.Bundle.toSpec, List.flatMap_map, Spec.TxOut.encode]
  have hJ : d.joinsplits.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec b.toSpec).joinSplits.isEmpty)
        (blake2b256 (personal "ZcashJSplitsHash")
          ((tx.toLegacySpec b.toSpec).joinSplits.flatMap Spec.JoinSplit.encode ++
            (tx.toLegacySpec b.toSpec).joinSplitPubKey.toList)) := by
    rw [hd']
    cases hs : tx.sproutBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.joinsplits = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map]
  have hSS : d.saplingSpends.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec b.toSpec).saplingSpends.isEmpty)
        (blake2b256 (personal "ZcashSSpendsHash")
          ((tx.toLegacySpec b.toSpec).saplingSpends.flatMap Spec.SpendV4.encode)) := by
    rw [hd']
    cases hs : tx.saplingBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.shieldedSpends = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map, Spec.SpendV4.encode, Sapling.SpendDescription.toSpecV4]
  have hSO : d.saplingOutputs.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec b.toSpec).saplingOutputs.isEmpty)
        (blake2b256 (personal "ZcashSOutputHash")
          ((tx.toLegacySpec b.toSpec).saplingOutputs.flatMap Spec.SaplingOutput.encode)) := by
    rw [hd']
    cases hs : tx.saplingBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.shieldedOutputs = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map, Spec.SaplingOutput.encode, Sapling.OutputDescription.toSpec]
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
  unfold v4SignatureHash
  simp only [SignableInput.hashType, Transparent.SighashType.encode]
  rcases hv with hv | hv <;>
    simp only [hv, TxVersion.hasOverwinter, Bool.not_true, Bool.false_eq_true, ite_false,
      hashLength?_32, personal?_16, some_bind', pure_bind, toState_absorbed, update_absorbed,
      updateHash_absorbed, hb, hvin, OutPoint.write_vec, unwrap_pure, Script.write_vec _ _ hsc,
      finalize_state_absorbed, hP, hS, hO, hJ, hSS, hSO, TxVersion.hasSapling] <;>
    simp only [Transparent.SIGHASH_ANYONECANPAY, Transparent.SIGHASH_MASK,
      Transparent.SIGHASH_SINGLE, Transparent.SIGHASH_NONE, Spec.legacySignatureDigest,
      TransactionData.toLegacySpec, hv, Spec.LegacyInput.hashType, htxin,
      Transparent.Bundle.txinToSpec, bne,
      Bool.not_not] <;>
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

/-- The transparent part the specification sees: the bundle's, or none. -/
def TransactionData.transparentSpec (tx : TransactionData) : Spec.Transparent :=
  (tx.transparentBundle.map Transparent.Bundle.toSpec).getD ⟨[], []⟩

/-- `hashLength?_32` in the `pure` form. -/
theorem hashLength?_32_pure :
    Blake2b.Params.new.hashLength? 32 = pure ⟨32, List.replicate 16 0⟩ := rfl

/-- `personal?_16` in the `pure` form. -/
theorem personal?_16_pure (p : Bytes 16) :
    (⟨32, List.replicate 16 0⟩ : Blake2b.Params).personal? (p.toList.map (·.toNat)) =
      pure (absorbed p []).state.params := personal?_16 p

/-- `SIGHASH_ALL`, a shielded signature's hash type, keeps every component digest. -/
theorem all_flags_v4 :
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_ANYONECANPAY == 0) = true ∧
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_MASK != Transparent.SIGHASH_SINGLE) = true ∧
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_MASK != Transparent.SIGHASH_NONE) = true :=
  by decide

/-- `v4_signature_hash` gives the digest a JoinSplit, Spend or binding signature signs. -/
theorem v4SignatureHash_shielded (tx : TransactionData) (hv : tx.version = .v3 ∨ tx.version = .v4)
    (hk : ∀ b, tx.transparentBundle = some b →
      ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) (d : Zip143Digests)
    (hd : zip143Digests tx = some d) :
    v4SignatureHash tx .shielded d = some (Spec.legacySignatureDigest blake2b256
      (tx.toLegacySpec tx.transparentSpec) .shielded).toList := by
  rw [zip143Digests_eq tx hk] at hd
  have hd' := (Option.some.inj hd).symm
  have hP : d.transparent.prevoutsDigest = (blake2b256 (personal "ZcashPrevoutHash")
      (tx.transparentSpec.vin.flatMap (·.prevout.encode))).toList := by
    rw [hd']
    cases hb : tx.transparentBundle with
    | none => simp [TransactionData.transparentSpec, hb]
    | some b =>
      simpa [TransactionData.transparentSpec, hb, List.flatMap_map, Spec.OutPoint.encode] using
        congrArg (fun l => (blake2b256 (personal "ZcashPrevoutHash")
          (List.flatMap Spec.OutPoint.encode l)).toList) (toSpec_prevouts b).symm
  have hS : d.transparent.sequenceDigest = (blake2b256 (personal "ZcashSequencHash")
      (tx.transparentSpec.vin.flatMap (Spec.u32 ·.nSequence))).toList := by
    rw [hd']
    cases hb : tx.transparentBundle with
    | none => simp [TransactionData.transparentSpec, hb]
    | some b =>
      simpa [TransactionData.transparentSpec, hb, List.flatMap_map] using
        congrArg (fun l => (blake2b256 (personal "ZcashSequencHash")
          (List.flatMap Spec.u32 l)).toList) (toSpec_sequences b).symm
  have hO : d.transparent.outputsDigest = (blake2b256 (personal "ZcashOutputsHash")
      (tx.transparentSpec.vout.flatMap Spec.TxOut.encode)).toList := by
    rw [hd']
    cases hb : tx.transparentBundle <;>
      simp [TransactionData.transparentSpec, hb, Transparent.Bundle.toSpec, List.flatMap_map,
        Spec.TxOut.encode]
  have hJ : d.joinsplits.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec tx.transparentSpec).joinSplits.isEmpty)
        (blake2b256 (personal "ZcashJSplitsHash")
          ((tx.toLegacySpec tx.transparentSpec).joinSplits.flatMap Spec.JoinSplit.encode ++
            (tx.toLegacySpec tx.transparentSpec).joinSplitPubKey.toList)) := by
    rw [hd']
    cases hs : tx.sproutBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.joinsplits = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map]
  have hSS : d.saplingSpends.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec tx.transparentSpec).saplingSpends.isEmpty)
        (blake2b256 (personal "ZcashSSpendsHash")
          ((tx.toLegacySpec tx.transparentSpec).saplingSpends.flatMap Spec.SpendV4.encode)) := by
    rw [hd']
    cases hs : tx.saplingBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.shieldedSpends = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map, Spec.SpendV4.encode, Sapling.SpendDescription.toSpecV4]
  have hSO : d.saplingOutputs.getD (List.replicate 32 0) =
      Spec.digestOrZero (!(tx.toLegacySpec tx.transparentSpec).saplingOutputs.isEmpty)
        (blake2b256 (personal "ZcashSOutputHash")
          ((tx.toLegacySpec tx.transparentSpec).saplingOutputs.flatMap
            Spec.SaplingOutput.encode)) := by
    rw [hd']
    cases hs : tx.saplingBundle with
    | none => simp [TransactionData.toLegacySpec, hs, Spec.digestOrZero]
    | some s =>
      by_cases he : s.shieldedOutputs = [] <;>
        simp [TransactionData.toLegacySpec, hs, he, Spec.digestOrZero, Option.filter,
          List.flatMap_map, Spec.SaplingOutput.encode, Sapling.OutputDescription.toSpec]
  have hpers : branchPersonalization (Spec.ascii "ZcashSigHash" 12) tx.consensusBranchId =
      ⟨(Spec.ascii "ZcashSigHash" 12).toList ++ Spec.u32 tx.consensusBranchId,
        by simp [Spec.ascii, Spec.u32, Spec.I2LEOSP]⟩ := rfl
  have hall := all_flags_v4
  unfold v4SignatureHash
  simp only [SignableInput.hashType, hall.1, hall.2.1, hall.2.2, Bool.and_self, ite_true]
  rcases hv with hv | hv <;>
    simp only [hv, TxVersion.hasOverwinter, TxVersion.hasSapling, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] <;>
    simp only [hashLength?_32_pure, personal?_16_pure, pure_bind, toState_absorbed,
      update_absorbed, updateHash_absorbed, finalize_state_absorbed, hP, hS, hO, hJ, hSS, hSO,
      ite_true] <;>
    simp only [Spec.legacySignatureDigest, TransactionData.toLegacySpec, hv,
      Spec.LegacyInput.hashType, Transparent.SIGHASH_ALL, toLeBytes_u32, toLeBytes_i64,
      Spec.digestOrZero, hpers, List.append_assoc, List.nil_append, List.append_nil,
      Bool.false_eq_true, ite_true, ite_false, some_eq_pure] <;>
    congr!

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.v4SignatureHash_transparent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v4SignatureHash_transparent

/--
info: 'ZcashSighash.Verifier.v4SignatureHash_shielded' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v4SignatureHash_shielded

end ZcashSighash.Verifier
