/-
The transcribed `zcash_primitives` computes the specification's digests, with BLAKE2b-256: the
transaction identifier, the authorizing data commitment and every signature hash of a version
5 or 6 transaction, under hypotheses that name what the Rust types allow and a transaction read
from its encoding never has.
-/
module

public import ZcashSighash.Proofs.Spec
public import ZcashSighash.Verifier.Sighash

@[expose] public section

namespace ZcashSighash.Verifier

open Spec (Byte Bytes personal)

/-! ## Hashing through `StateWrite` -/

/-- A state that has absorbed `x`, personalized with `p`. -/
def absorbed (p : Bytes 16) (x : List Byte) : StateWrite :=
  ⟨⟨⟨32, p.toList.map (·.toNat)⟩, x.map (·.toNat)⟩⟩

/-- `hasher p` never panics: it is the empty state personalized with `p`. -/
theorem hasher_eq (p : Bytes 16) : hasher p = some (absorbed p []) := by
  simp [hasher, Blake2b.Params.new, Blake2b.Params.hashLength?, Blake2b.Params.personal?,
    Blake2b.outBytes, Blake2b.personalBytes, Blake2b.Params.toState, absorbed]

/-- Writing `b` to a state that has absorbed `x` succeeds, and the state has absorbed
    `x ++ b`. -/
theorem writeAll_absorbed (p : Bytes 16) (x b : List Byte) :
    (absorbed p x).writeAll b = .ok (absorbed p (x ++ b)) := by
  simp [StateWrite.writeAll, absorbed, Blake2b.State.update]

/-- `writeAll_absorbed` through the `Write` class, as the writers generic over their output
    (`Vector::write`, `OutPoint::write`) call it. -/
theorem classWrite_absorbed (p : Bytes 16) (x b : List Byte) :
    Write.writeAll (absorbed p x) b = .ok (absorbed p (x ++ b)) :=
  writeAll_absorbed p x b

/-- Finalizing a state that has absorbed `x` gives the specification's BLAKE2b-256 of `x`. -/
theorem finalize_absorbed (p : Bytes 16) (x : List Byte) :
    (absorbed p x).finalize = (blake2b256 p x).toList := rfl

/-- `unwrap` of a success is that value: no panic. -/
theorem unwrap_ok {ε α : Type} (a : α) : unwrap (Except.ok a : Except ε α) = some a := rfl

/-- `u32::to_le_bytes` is the specification's `uint32` encoding. -/
theorem toLeBytes_u32 (x : BitVec 32) : toLeBytes 4 x = Spec.u32 x := rfl

/-- `i64::to_le_bytes` is the specification's `int64` encoding. -/
theorem toLeBytes_i64 (x : BitVec 64) : toLeBytes 8 x = Spec.i64 x := rfl

/-- `write_u32_le` absorbs the value's `uint32` encoding. -/
theorem writeU32Le_absorbed (p : Bytes 16) (x : List Byte) (v : BitVec 32) :
    (absorbed p x).writeU32Le v = .ok (absorbed p (x ++ Spec.u32 v)) :=
  writeAll_absorbed p x _

/-- `CompactSize::write_unbounded` absorbs the specification's `compactSize` encoding, for any
    `u64`. -/
theorem writeUnbounded_absorbed (p : Bytes 16) (x : List Byte) (v : BitVec 64) :
    CompactSize.writeUnbounded (absorbed p x) v =
      .ok (absorbed p (x ++ Spec.compactSize v)) := by
  unfold CompactSize.writeUnbounded Spec.compactSize
  dsimp only
  split_ifs <;>
    simp [classWrite_absorbed, toLeBytes, Spec.I2LEOSP, List.range_succ, bind, Except.bind] <;>
    rw [Nat.mod_eq_of_lt (by omega)] <;> simp [BitVec.ofNat_toNat]

/-- A `compactSize` up to `MAX_COMPACT_SIZE` is written as the specification encodes it. -/
theorem compactSizeWrite_absorbed (p : Bytes 16) (x : List Byte) (n : ℕ)
    (hn : n ≤ MAX_COMPACT_SIZE) :
    CompactSize.write (absorbed p x) n =
      .ok (absorbed p (x ++ Spec.compactSize (BitVec.ofNat 64 n))) := by
  simp [CompactSize.write, Nat.not_lt.mpr hn, writeUnbounded_absorbed]

/-- A loop that writes `f a` for each `a` absorbs their concatenation. -/
theorem forIn_absorbed {α : Type} (l : List α) (p : Bytes 16) (x : List Byte)
    (f : α → List Byte) (body : α → StateWrite → Option StateWrite)
    (hb : ∀ a ∈ l, ∀ y, body a (absorbed p y) = some (absorbed p (y ++ f a))) :
    forIn l (absorbed p x) (fun a r => (body a r).bind fun r => some (ForInStep.yield r)) =
      some (absorbed p (x ++ l.flatMap f)) := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons, hb a List.mem_cons_self, Option.bind_eq_bind, Option.bind_some]
    simpa [List.append_assoc] using
      ih (x ++ f a) (fun a h => hb a (List.mem_cons_of_mem _ h))

/-- A fold that writes `f a` for each `a` absorbs their concatenation. -/
theorem foldlM_absorbed {α : Type} (l : List α) (p : Bytes 16) (x : List Byte)
    (f : α → List Byte) (func : StateWrite → α → IoResult StateWrite)
    (hf : ∀ a ∈ l, ∀ y, func (absorbed p y) a = .ok (absorbed p (y ++ f a))) :
    l.foldlM func (absorbed p x) = .ok (absorbed p (x ++ l.flatMap f)) := by
  induction l generalizing x with
  | nil => simp [pure, Except.pure]
  | cons a l ih =>
    simp only [List.foldlM_cons, hf a List.mem_cons_self, bind, Except.bind]
    simpa [List.append_assoc] using
      ih (x ++ f a) (fun a h => hf a (List.mem_cons_of_mem _ h))

/-- A script no longer than `MAX_COMPACT_SIZE` is written as the specification's `script`
    field: its `compactSize` length, then its bytes. -/
theorem Script.write_absorbed (s : Transparent.Script) (p : Bytes 16) (x : List Byte)
    (hs : s.code.length ≤ MAX_COMPACT_SIZE) :
    s.write (absorbed p x) = .ok (absorbed p (x ++ Spec.script s.code)) := by
  simp only [Transparent.Script.write, Vector.write, compactSizeWrite_absorbed p x _ hs, bind,
    Except.bind]
  rw [foldlM_absorbed s.code p _ (fun e => [e]) _ fun e _ y => classWrite_absorbed p y [e]]
  simp [Spec.script]

/-- An outpoint is written as its field encoding: the 32-byte hash, then the `uint32` index. -/
theorem OutPoint.write_absorbed (o : Transparent.OutPoint) (p : Bytes 16) (x : List Byte) :
    o.write (absorbed p x) = .ok (absorbed p (x ++ (o.hash.toList ++ Spec.u32 o.n))) := by
  simp [Transparent.OutPoint.write, classWrite_absorbed, bind, Except.bind, toLeBytes_u32]

/-- An output whose script fits in a `compactSize` is written as its field encoding: the
    `int64` value, then the script. -/
theorem TxOut.write_absorbed (o : Transparent.TxOut) (p : Bytes 16) (x : List Byte)
    (hs : o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    o.write (absorbed p x) =
      .ok (absorbed p (x ++ (Spec.i64 o.value ++ Spec.script o.scriptPubkey.code))) := by
  simp [Transparent.TxOut.write, classWrite_absorbed, bind, Except.bind, toLeBytes_i64,
    Script.write_absorbed _ _ _ hs]

/-- `self` with `b` absorbed. -/
def StateWrite.append (self : StateWrite) (b : List Byte) : StateWrite :=
  ⟨self.state.update (b.map (·.toNat))⟩

/-- `write_all` on any state succeeds and appends. Loops over several hashers use this form,
    since their states are not all `absorbed` at once. -/
theorem writeAll_eq (s : StateWrite) (b : List Byte) : s.writeAll b = .ok (s.append b) := rfl

/-- Appending `b` to a state that has absorbed `x` gives one that has absorbed `x ++ b`. -/
theorem append_absorbed (p : Bytes 16) (x b : List Byte) :
    (absorbed p x).append b = absorbed p (x ++ b) := by
  simp [StateWrite.append, absorbed, Blake2b.State.update]

/-- Two appends are one append of the concatenation. -/
theorem append_append (s : StateWrite) (x y : List Byte) :
    (s.append x).append y = s.append (x ++ y) := by
  simp [StateWrite.append, Blake2b.State.update, List.append_assoc]

/-- A loop whose body always continues with `step` is a fold. -/
theorem forIn_yield {α σ : Type} (l : List α) (init : σ) (body : α → σ → Option (ForInStep σ))
    (step : α → σ → σ) (hb : ∀ a ∈ l, ∀ s, body a s = some (.yield (step a s))) :
    forIn l init body = some (l.foldl (fun s a => step a s) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, hb a List.mem_cons_self, Option.bind_eq_bind, Option.bind_some,
      List.foldl_cons]
    exact ih _ fun a h => hb a (List.mem_cons_of_mem _ h)

/-- Appending `f a` for each `a` appends their concatenation. -/
theorem foldl_append_absorbed {α : Type} (l : List α) (p : Bytes 16) (x : List Byte)
    (f : α → List Byte) :
    l.foldl (fun s a => s.append (f a)) (absorbed p x) = absorbed p (x ++ l.flatMap f) := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [append_absorbed, ih, List.append_assoc]

/-- A fold over pairs is a pair of folds. -/
theorem foldl_prod {α σ τ : Type} (l : List α) (x : σ) (y : τ) (F : σ → α → σ)
    (G : τ → α → τ) :
    l.foldl (fun s a => (F s.1 a, G s.2 a)) (x, y) = (l.foldl F x, l.foldl G y) := by
  induction l generalizing x y with
  | nil => rfl
  | cons a l ih => exact ih _ _

/-- A fold over triples is a triple of folds. -/
theorem foldl_prod3 {α σ τ υ : Type} (l : List α) (x : σ) (y : τ) (z : υ) (F : σ → α → σ)
    (G : τ → α → τ) (K : υ → α → υ) :
    l.foldl (fun s a => (F s.1 a, G s.2.1 a, K s.2.2 a)) (x, y, z) =
      (l.foldl F x, l.foldl G y, l.foldl K z) := by
  induction l generalizing x y z with
  | nil => rfl
  | cons a l ih => exact ih _ _ _

/-! ## The specification's view of a `TransactionData` -/

/-- The empty Sapling component. -/
def emptySapling : Spec.Sapling :=
  ⟨[], [], 0, List.Vector.replicate 32 0, List.Vector.replicate 64 0⟩

/-- The empty Orchard-shaped component. -/
def emptyOrchard : Spec.OrchardBundle :=
  ⟨[], 0, 0, List.Vector.replicate 32 0, [], List.Vector.replicate 64 0⟩

/-- The input at `i`, spending the coin its authorizing context gives. -/
def Transparent.Bundle.txinToSpec (b : Transparent.Bundle) (i : ℕ) (x : Transparent.TxIn) :
    Spec.TxIn :=
  ⟨⟨x.prevout.hash, x.prevout.n⟩, x.sequence,
    ⟨b.authorization.inputAmounts.getD i 0, (b.authorization.inputScriptpubkeys.getD i ⟨[]⟩).code⟩⟩

/-- A transparent bundle's inputs and outputs. -/
def Transparent.Bundle.toSpec (b : Transparent.Bundle) : Spec.Transparent :=
  ⟨b.vin.mapIdx b.txinToSpec, b.vout.map fun o => ⟨o.value, o.scriptPubkey.code⟩⟩

/-- A Sapling bundle, its anchor that of its first spend. -/
def Sapling.Bundle.toSpec (b : Sapling.Bundle) : Spec.Sapling :=
  ⟨b.shieldedSpends.map fun s => ⟨s.cv, s.nullifier, s.rk, s.zkproof, s.spendAuthSig⟩,
    b.shieldedOutputs.map fun o =>
      ⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext, o.outCiphertext, o.zkproof⟩,
    b.valueBalance, (b.shieldedSpends.head?.map (·.anchor)).getD (List.Vector.replicate 32 0),
    b.bindingSig⟩

/-- An Orchard-shaped bundle. -/
def Orchard.Bundle.toSpec (b : Orchard.Bundle) : Spec.OrchardBundle :=
  ⟨b.actions.toList.map fun a =>
      ⟨a.cvNet, a.nf, a.rk, a.cmx, a.epkBytes, a.encCiphertext, a.outCiphertext, a.authorization⟩,
    b.flagByte, b.valueBalance, b.anchor, b.proof, b.bindingSignature⟩

/-- A version 5 or 6 transaction's data, as the specification's transaction. -/
def TransactionData.toSpec (tx : TransactionData) : Spec.Transaction where
  format := match tx.version with
    | .v6 => .v6 ((tx.ironwoodBundle.map Orchard.Bundle.toSpec).getD emptyOrchard)
    | _ => .v5
  header := ⟨tx.version.header, tx.version.versionGroupId, tx.consensusBranchId, tx.lockTime,
    tx.expiryHeight⟩
  transparent := (tx.transparentBundle.map Transparent.Bundle.toSpec).getD ⟨[], []⟩
  scriptSigs := ((tx.transparentBundle.map fun b => b.vin.map (·.scriptSig.code))).getD []
  sapling := (tx.saplingBundle.map Sapling.Bundle.toSpec).getD emptySapling
  orchard := (tx.orchardBundle.map Orchard.Bundle.toSpec).getD emptyOrchard

/-! ## The transaction identifier's components -/

/-- `transparent_prevout_hash` is §T.2a's digest of the inputs' outpoints. -/
theorem transparentPrevoutHash_eq (vin : List Transparent.TxIn) :
    transparentPrevoutHash vin = some (blake2b256 (personal "ZTxIdPrevoutHash")
      (vin.flatMap fun i => i.prevout.hash.toList ++ Spec.u32 i.prevout.n)).toList := by
  simp only [transparentPrevoutHash, hasher_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [forIn_absorbed vin _ _
    (fun i : Transparent.TxIn => i.prevout.hash.toList ++ Spec.u32 i.prevout.n)
    (fun (a : Transparent.TxIn) r => unwrap (a.prevout.write r))
    (fun _ _ _ => by simp [OutPoint.write_absorbed, unwrap_ok])]
  simp [finalize_absorbed]

/-- `transparent_sequence_hash` is §T.2b's digest of the inputs' sequence numbers. -/
theorem transparentSequenceHash_eq (vin : List Transparent.TxIn) :
    transparentSequenceHash vin = some (blake2b256 (personal "ZTxIdSequencHash")
      (vin.flatMap fun i => Spec.u32 i.sequence)).toList := by
  simp only [transparentSequenceHash, hasher_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [forIn_absorbed vin _ _ (fun i : Transparent.TxIn => Spec.u32 i.sequence)
    (fun (a : Transparent.TxIn) r => unwrap (r.writeU32Le a.sequence))
    (fun _ _ _ => by simp [writeU32Le_absorbed, unwrap_ok])]
  simp [finalize_absorbed]

/-- `transparent_outputs_hash` is §T.2c's digest of the outputs, when their scripts fit in a
    `compactSize`. -/
theorem transparentOutputsHash_eq (vout : List Transparent.TxOut)
    (hk : ∀ o ∈ vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    transparentOutputsHash vout = some (blake2b256 (personal "ZTxIdOutputsHash")
      (vout.flatMap fun o => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)).toList := by
  simp only [transparentOutputsHash, hasher_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [forIn_absorbed vout _ _
    (fun o : Transparent.TxOut => Spec.i64 o.value ++ Spec.script o.scriptPubkey.code)
    (fun (a : Transparent.TxOut) r => unwrap (a.write r))
    (fun o ho _ => by simp [TxOut.write_absorbed _ _ _ (hk o ho), unwrap_ok])]
  simp [finalize_absorbed]


/-- Mapping `g` over `mapIdx f` forgets the index when `g ∘ f i` does not use it. -/
theorem map_mapIdx {α β γ : Type} (l : List α) (f : ℕ → α → β) (g : β → γ) (h : α → γ)
    (hg : ∀ i a, g (f i a) = h a) : (l.mapIdx f).map g = l.map h := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [hg]

/-- The specification's inputs have the bundle's outpoints. -/
theorem toSpec_prevouts (b : Transparent.Bundle) :
    b.toSpec.vin.map (·.prevout) = b.vin.map fun x => ⟨x.prevout.hash, x.prevout.n⟩ :=
  map_mapIdx _ _ _ _ fun _ _ => rfl

/-- The specification's inputs have the bundle's sequence numbers. -/
theorem toSpec_sequences (b : Transparent.Bundle) :
    b.toSpec.vin.map (·.nSequence) = b.vin.map (·.sequence) :=
  map_mapIdx _ _ _ _ fun _ _ => rfl

/-- `transparent_digests` gives §T.2a–c's three digests of the bundle. -/
theorem transparentDigests_eq (b : Transparent.Bundle)
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) :
    transparentDigests b = some ⟨(Spec.prevoutsDigest blake2b256 b.toSpec).toList,
      (Spec.sequenceDigest blake2b256 b.toSpec).toList,
      (Spec.outputsDigest blake2b256 b.toSpec).toList⟩ := by
  have hp : b.toSpec.vin.flatMap (·.prevout.encode) =
      b.vin.flatMap fun i => i.prevout.hash.toList ++ Spec.u32 i.prevout.n := by
    simpa [List.flatMap_map, Spec.OutPoint.encode] using
      congrArg (List.flatMap Spec.OutPoint.encode) (toSpec_prevouts b)
  have hs : b.toSpec.vin.flatMap (Spec.u32 ·.nSequence) =
      b.vin.flatMap fun i => Spec.u32 i.sequence := by
    simpa [List.flatMap_map] using congrArg (List.flatMap Spec.u32) (toSpec_sequences b)
  simp only [transparentDigests, transparentPrevoutHash_eq, transparentSequenceHash_eq,
    transparentOutputsHash_eq _ hk, Spec.prevoutsDigest, Spec.sequenceDigest,
    Spec.outputsDigest, hp, hs]
  simp [Transparent.Bundle.toSpec, List.flatMap_map, Spec.TxOut.encode]

/-- With no transparent bundle, `hash_transparent_txid_data` is §T.2's empty digest. -/
theorem hashTransparentTxidData_none :
    hashTransparentTxidData none = some (Spec.transparentDigest blake2b256 ⟨[], []⟩).toList := by
  simp [hashTransparentTxidData, hasher_eq, finalize_absorbed, Spec.transparentDigest]

/-- For a bundle with an input or an output, `hash_transparent_txid_data` of its three digests
    is §T.2's digest. An empty bundle is hashed differently. -/
theorem hashTransparentTxidData_some (b : Transparent.Bundle) (hb : b.vin ≠ [] ∨ b.vout ≠ []) :
    hashTransparentTxidData (some ⟨(Spec.prevoutsDigest blake2b256 b.toSpec).toList,
      (Spec.sequenceDigest blake2b256 b.toSpec).toList,
      (Spec.outputsDigest blake2b256 b.toSpec).toList⟩) =
      some (Spec.transparentDigest blake2b256 b.toSpec).toList := by
  have hne : ¬(b.toSpec.vin.isEmpty && b.toSpec.vout.isEmpty) := by
    simp only [Transparent.Bundle.toSpec, List.isEmpty_iff, List.mapIdx_eq_nil_iff,
      List.map_eq_nil_iff, Bool.and_eq_true]
    tauto
  simp [hashTransparentTxidData, hasher_eq, writeAll_absorbed, unwrap_ok, finalize_absorbed,
    Spec.transparentDigest, hne, Spec.node, bind]

/-- `hash_header_txid_data` is §T.1's header digest. -/
theorem hashHeaderTxidData_eq (tx : TransactionData) :
    hashHeaderTxidData tx.version tx.consensusBranchId tx.lockTime tx.expiryHeight =
      some (Spec.headerDigest blake2b256 tx.toSpec.header).toList := by
  simp [hashHeaderTxidData, hasher_eq, writeU32Le_absorbed, unwrap_ok, finalize_absorbed,
    Spec.headerDigest, TransactionData.toSpec, bind]

/-- `hash_sapling_spends` is §T.3a's digest (in version 6, ZIP 229's without the anchor), when
    every spend has the bundle's anchor. The Rust hashes each spend's own anchor. -/
theorem hashSaplingSpends_eq (version : TxVersion) (b : Sapling.Bundle)
    (ha : ∀ s ∈ b.shieldedSpends, s.anchor = b.toSpec.anchor) (f : Spec.Format)
    (hf : f.IsV6 = version.hasIronwood) :
    hashSaplingSpends version b.shieldedSpends =
      some (Spec.saplingSpendsDigest blake2b256 f b.toSpec).toList := by
  by_cases hs : b.shieldedSpends = []
  · simp [hashSaplingSpends, hs, hasher_eq, finalize_absorbed, Spec.saplingSpendsDigest,
      Sapling.Bundle.toSpec]
  have hs' : b.toSpec.spends ≠ [] := by simpa [Sapling.Bundle.toSpec] using hs
  simp only [hashSaplingSpends, hasher_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Spec.saplingSpendsDigest, hs', ite_false]
  rw [ite_eq_left (by simpa using hs)]
  rw [forIn_yield _ _ _ (fun (s : Sapling.SpendDescription) st =>
    (st.1.append s.nullifier.toList, st.2.append (s.cv.toList ++
      (if version.hasIronwood then [] else s.anchor.toList) ++ s.rk.toList)))
    (fun a _ st => by cases version <;> simp [writeAll_eq, unwrap_ok, append_append,
      TxVersion.hasIronwood])]
  rw [foldl_prod _ _ _ (fun (s : StateWrite) (a : Sapling.SpendDescription) =>
      s.append a.nullifier.toList)
    (fun (s : StateWrite) (a : Sapling.SpendDescription) => s.append (a.cv.toList ++
      (if version.hasIronwood then [] else a.anchor.toList) ++ a.rk.toList)),
    foldl_append_absorbed, foldl_append_absorbed]
  simp only [Option.bind_some, writeAll_absorbed, unwrap_ok, finalize_absorbed]
  have hflat : b.shieldedSpends.flatMap (fun a => a.cv.toList ++ a.anchor.toList ++ a.rk.toList) =
      b.shieldedSpends.flatMap (fun a => a.cv.toList ++ b.toSpec.anchor.toList ++ a.rk.toList) :=
    List.flatMap_congr fun a h => by rw [ha a h]
  cases version <;>
    simp_all [Spec.node, Spec.saplingSpendsCompactDigest, Spec.saplingSpendsNoncompactDigest,
      Sapling.Bundle.toSpec, List.flatMap_map, saplingSpendsNoncompactPersonalization,
      TxVersion.hasIronwood]


/-- `hash_sapling_outputs` is §T.3b's digest. -/
theorem hashSaplingOutputs_eq (b : Sapling.Bundle) :
    hashSaplingOutputs b.shieldedOutputs =
      some (Spec.saplingOutputsDigest blake2b256 b.toSpec).toList := by
  by_cases ho : b.shieldedOutputs = []
  · simp [hashSaplingOutputs, ho, hasher_eq, finalize_absorbed, Spec.saplingOutputsDigest,
      Sapling.Bundle.toSpec]
  have ho' : b.toSpec.outputs ≠ [] := by simpa [Sapling.Bundle.toSpec] using ho
  simp only [hashSaplingOutputs, hasher_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Spec.saplingOutputsDigest, ho', ite_false]
  rw [ite_eq_left (by simpa using ho)]
  rw [forIn_yield _ _ _ (fun (o : Sapling.OutputDescription) st =>
    (st.1.append (o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52),
      st.2.1.append ((o.encCiphertext.toList.drop 52).take (564 - 52)),
      st.2.2.append (o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)))
    (fun a _ st => by simp [writeAll_eq, unwrap_ok, append_append])]
  rw [foldl_prod3 _ _ _ _
    (fun (s : StateWrite) (o : Sapling.OutputDescription) => s.append
      (o.cmu.toList ++ o.ephemeralKey.toList ++ o.encCiphertext.toList.take 52))
    (fun (s : StateWrite) (o : Sapling.OutputDescription) => s.append
      ((o.encCiphertext.toList.drop 52).take (564 - 52)))
    (fun (s : StateWrite) (o : Sapling.OutputDescription) => s.append
      (o.cv.toList ++ o.encCiphertext.toList.drop 564 ++ o.outCiphertext.toList)),
    foldl_append_absorbed, foldl_append_absorbed, foldl_append_absorbed]
  simp [writeAll_absorbed, unwrap_ok, finalize_absorbed, Spec.node,
    Spec.saplingOutputsCompactDigest, Spec.saplingOutputsMemosDigest,
    Spec.saplingOutputsNoncompactDigest, Sapling.Bundle.toSpec, List.flatMap_map]


/-- `hash_sapling_txid_data` is §T.3's Sapling digest, when every spend has the bundle's
    anchor. -/
theorem hashSaplingTxidData_eq (version : TxVersion) (b : Sapling.Bundle)
    (ha : ∀ s ∈ b.shieldedSpends, s.anchor = b.toSpec.anchor) (f : Spec.Format)
    (hf : f.IsV6 = version.hasIronwood) :
    hashSaplingTxidData version b = some (Spec.saplingDigest blake2b256 f b.toSpec).toList := by
  by_cases he : b.shieldedSpends = [] ∧ b.shieldedOutputs = []
  · simp [hashSaplingTxidData, he, hasher_eq, finalize_absorbed, Spec.saplingDigest,
      Sapling.Bundle.toSpec]
  have he' : ¬(b.toSpec.spends = [] ∧ b.toSpec.outputs = []) := by
    simpa [Sapling.Bundle.toSpec] using he
  have he'' : (!(b.shieldedSpends.isEmpty && b.shieldedOutputs.isEmpty)) = true := by
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, List.isEmpty_eq_false_iff]
    tauto
  simp [hashSaplingTxidData, he'', hasher_eq, hashSaplingSpends_eq version b ha f hf,
    hashSaplingOutputs_eq, writeAll_absorbed, unwrap_ok, finalize_absorbed, Spec.saplingDigest,
    he', toLeBytes_i64, bind]
  rfl

/-- `hash_sapling_txid_empty` is the hash of no bytes under `ZTxIdSaplingHash`. -/
theorem hashSaplingTxidEmpty_eq :
    hashSaplingTxidEmpty = some (blake2b256 (personal "ZTxIdSaplingHash") []).toList := by
  simp [hashSaplingTxidEmpty, hasher_eq, finalize_absorbed]

/-- The specification's Sapling digest of no spends or outputs is that same empty hash. -/
theorem saplingDigest_empty (H : Spec.Hash) (f : Spec.Format) :
    Spec.saplingDigest H f emptySapling = H (personal "ZTxIdSaplingHash") [] := by
  simp [Spec.saplingDigest, emptySapling]


/-- The specification's personalizations of a commitment format. -/
def Orchard.Personalizations.toSpec (p : Orchard.Personalizations) : Spec.Personalizations :=
  ⟨p.bundle, p.actionsCompact, p.actionsMemos, p.actionsNoncompact, p.auth⟩

/-- `orchard`'s `hasher p` never panics: it is the empty state personalized with `p`. The
    `orchard` crate hashes through `blake2b_simd`'s `State` directly, not a `StateWrite`. -/
theorem orchard_absorbed (p : Bytes 16) :
    Orchard.hasher p = some (absorbed p []).state := by
  simp [Orchard.hasher, Blake2b.Params.new, Blake2b.Params.hashLength?, Blake2b.Params.personal?,
    Blake2b.outBytes, Blake2b.personalBytes, Blake2b.Params.toState, absorbed]

/-- Two `update`s are one `update` with the concatenation. -/
theorem update_update (s : Blake2b.State) (x y : List Byte) :
    Orchard.update (Orchard.update s x) y = Orchard.update s (x ++ y) := by
  simp [Orchard.update, Blake2b.State.update, List.append_assoc]

/-- `update` with `b` on a state that has absorbed `x` gives one that has absorbed `x ++ b`. -/
theorem update_absorbed (p : Bytes 16) (x b : List Byte) :
    Orchard.update (absorbed p x).state b = (absorbed p (x ++ b)).state := by
  simp [Orchard.update, absorbed, Blake2b.State.update]

/-- Finalizing a state that has absorbed `x` gives the specification's BLAKE2b-256 of `x`. -/
theorem finalize_state_absorbed (p : Bytes 16) (x : List Byte) :
    Orchard.finalize (absorbed p x).state = (blake2b256 p x).toList := rfl

/-- `update` with `f a` for each `a` absorbs their concatenation. -/
theorem foldl_update_absorbed {α : Type} (l : List α) (p : Bytes 16) (x : List Byte)
    (f : α → List Byte) :
    l.foldl (fun s a => Orchard.update s (f a)) (absorbed p x).state =
      (absorbed p (x ++ l.flatMap f)).state := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [update_absorbed, ih, List.append_assoc]

/-- `hash_bundle_txid_data` is §T.4's digest under the bundle's commitment format: its
    personalizations, and the anchor exactly when the format includes it. -/
theorem hashBundleTxidData_eq (b : Orchard.Bundle) (v : Orchard.TxVersion)
    (format : Orchard.BundleCommitmentFormat) (hf : b.valuePool.commitmentFormat v = .ok format) :
    Orchard.hashBundleTxidData b v = some (.ok (Spec.actionsDigest blake2b256
      format.personalizations.toSpec (!format.includesAnchorInTxidDigest) b.toSpec).toList) := by
  simp only [Orchard.hashBundleTxidData, hf, orchard_absorbed, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some]
  rw [forIn_yield _ _ _ (fun (a : Orchard.Action) st =>
    (Orchard.update st.1 (a.nf.toList ++ a.cmx.toList ++ a.epkBytes.toList ++
        a.encCiphertext.toList.take 52),
      Orchard.update st.2.1 ((a.encCiphertext.toList.drop 52).take (564 - 52)),
      Orchard.update st.2.2 (a.cvNet.toList ++ a.rk.toList ++ a.encCiphertext.toList.drop 564 ++
        a.outCiphertext.toList)))
    (fun a _ st => by simp [update_update])]
  rw [foldl_prod3 _ _ _ _
    (fun (s : Blake2b.State) (a : Orchard.Action) => Orchard.update s (a.nf.toList ++
      a.cmx.toList ++ a.epkBytes.toList ++ a.encCiphertext.toList.take 52))
    (fun (s : Blake2b.State) (a : Orchard.Action) =>
      Orchard.update s ((a.encCiphertext.toList.drop 52).take (564 - 52)))
    (fun (s : Blake2b.State) (a : Orchard.Action) => Orchard.update s (a.cvNet.toList ++
      a.rk.toList ++ a.encCiphertext.toList.drop 564 ++ a.outCiphertext.toList)),
    foldl_update_absorbed, foldl_update_absorbed, foldl_update_absorbed]
  cases format <;>
    simp [Orchard.BundleCommitmentFormat.includesAnchorInTxidDigest, update_absorbed,
      finalize_state_absorbed, Spec.actionsDigest, Orchard.Bundle.toSpec,
      Orchard.NonEmpty.toList, List.flatMap_map, toLeBytes_i64, Orchard.Personalizations.toSpec]


/-- `hash_bundle_txid_empty` is the specification's digest of no actions under the format's
    personalizations; with no actions the anchor flag does not matter. -/
theorem hashBundleTxidEmpty_eq (vp : Orchard.ValuePool) (v : Orchard.TxVersion)
    (format : Orchard.BundleCommitmentFormat) (hf : vp.commitmentFormat v = .ok format)
    (anchor : Bool) :
    Orchard.hashBundleTxidEmpty vp v = some (.ok (Spec.actionsDigest blake2b256
      format.personalizations.toSpec anchor emptyOrchard).toList) := by
  simp [Orchard.hashBundleTxidEmpty, hf, orchard_absorbed, finalize_state_absorbed,
    Spec.actionsDigest, emptyOrchard, Orchard.Personalizations.toSpec]

/-- The Rust's `"ZcashTxHash_" || CONSENSUS_BRANCH_ID` is the specification's. -/
theorem txHashPersonalization_eq (b : BitVec 32) :
    branchPersonalization (Spec.ascii "ZcashTxHash_" 12) b = Spec.txHashPersonalization b := rfl

/-- The Rust's `"ZTxAuthHash_" || CONSENSUS_BRANCH_ID` is the specification's. -/
theorem authPersonalization_eq (b : BitVec 32) :
    branchPersonalization (Spec.ascii "ZTxAuthHash_" 12) b = Spec.authPersonalization b := rfl


/-- Spends sharing one anchor share the first's. -/
theorem anchor_toSpec (b : Sapling.Bundle)
    (ha : ∀ s ∈ b.shieldedSpends, ∀ s' ∈ b.shieldedSpends, s.anchor = s'.anchor) :
    ∀ s ∈ b.shieldedSpends, s.anchor = b.toSpec.anchor := by
  intro s hs
  cases hsp : b.shieldedSpends with
  | nil => simp [hsp] at hs
  | cons s₀ rest =>
    simp only [Sapling.Bundle.toSpec, hsp, List.head?_cons, Option.map_some, Option.getD_some]
    exact ha s hs s₀ (by simp [hsp])

/-- An Orchard bundle in version 5 is hashed as §T.4 says, anchor included. -/
theorem hashBundleTxidData_orchardV5 (b : Orchard.Bundle) (hp : b.valuePool = .orchard) :
    Orchard.hashBundleTxidData b .v5 =
      some (.ok (Spec.actionsDigest blake2b256 Spec.orchardV5 false b.toSpec).toList) :=
  hashBundleTxidData_eq b .v5 .orchardV5 (by simp [hp, Orchard.ValuePool.commitmentFormat])

/-- An Orchard bundle in version 6 is hashed as ZIP 229 says: `_v6` personalization, no
    anchor. -/
theorem hashBundleTxidData_orchardV6 (b : Orchard.Bundle) (hp : b.valuePool = .orchard) :
    Orchard.hashBundleTxidData b .v6 =
      some (.ok (Spec.actionsDigest blake2b256 Spec.orchardV6 true b.toSpec).toList) :=
  hashBundleTxidData_eq b .v6 .orchardV6 (by simp [hp, Orchard.ValuePool.commitmentFormat])

/-- An Ironwood bundle is hashed as ZIP 229 says: Ironwood's personalizations, no anchor. -/
theorem hashBundleTxidData_ironwoodV6 (b : Orchard.Bundle) (hp : b.valuePool = .ironwood) :
    Orchard.hashBundleTxidData b .v6 =
      some (.ok (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList) :=
  hashBundleTxidData_eq b .v6 .ironwoodV6 (by simp [hp, Orchard.ValuePool.commitmentFormat])

/-- The Orchard personalizations of a version. -/
def orchardPersonalizations (version : TxVersion) : Spec.Personalizations :=
  if version.hasIronwood then Spec.orchardV6 else Spec.orchardV5

/-- `TxIdDigester::digest_orchard` gives the specification's Orchard digest of the bundle, if
    any, when it is in the Orchard pool. -/
theorem digestOrchard_eq (version : TxVersion) (ob : Option Orchard.Bundle)
    (ho : ∀ b, ob = some b → b.valuePool = .orchard) :
    TxIdDigester.digestOrchard version ob = some (ob.map fun b => (Spec.actionsDigest blake2b256
      (orchardPersonalizations version) version.hasIronwood b.toSpec).toList) := by
  cases ob with
  | none => rfl
  | some b =>
    have hp := ho b rfl
    cases version <;>
      simp [TxIdDigester.digestOrchard, orchardCommitmentDomain, hashBundleTxidData_orchardV5 b hp,
        hashBundleTxidData_orchardV6 b hp, unwrap_ok, orchardPersonalizations,
        TxVersion.hasIronwood]


/-- `TxIdDigester::digest_ironwood` gives ZIP 229's Ironwood digest of the bundle, if any,
    when it is in the Ironwood pool. -/
theorem digestIronwood_eq (ib : Option Orchard.Bundle)
    (hi : ∀ b, ib = some b → b.valuePool = .ironwood) :
    TxIdDigester.digestIronwood ib = some (ib.map fun b =>
      (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList) := by
  cases ib with
  | none => rfl
  | some b =>
    simp [TxIdDigester.digestIronwood, ironwoodV6Domain, hashBundleTxidData_ironwoodV6 b (hi b rfl),
      unwrap_ok]

/-- The hypotheses under which the transcription computes the specification's digests. A
    version 5 or 6 transaction read from its encoding satisfies them (`readV5_wellFormed`,
    `readV6_wellFormed`, `Proofs/Read.lean`): its transparent and Sapling bundles, if any, are
    not empty; its Sapling spends share one anchor; its Orchard and Ironwood bundles are in
    their pools; and no script in it exceeds `MAX_COMPACT_SIZE`. -/
structure WellFormed (tx : TransactionData) : Prop where
  version : tx.version = .v5 ∨ tx.version = .v6
  transparentNonempty : ∀ b, tx.transparentBundle = some b → b.vin ≠ [] ∨ b.vout ≠ []
  outputScripts : ∀ b, tx.transparentBundle = some b →
    ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE
  saplingAnchor : ∀ b, tx.saplingBundle = some b →
    ∀ s ∈ b.shieldedSpends, ∀ s' ∈ b.shieldedSpends, s.anchor = s'.anchor
  orchardPool : ∀ b, tx.orchardBundle = some b → b.valuePool = .orchard
  ironwoodPool : ∀ b, tx.ironwoodBundle = some b → b.valuePool = .ironwood
  scriptSigs : ∀ b, tx.transparentBundle = some b →
    ∀ i ∈ b.vin, i.scriptSig.code.length ≤ MAX_COMPACT_SIZE
  saplingNonempty : ∀ b, tx.saplingBundle = some b →
    b.shieldedSpends ≠ [] ∨ b.shieldedOutputs ≠ []

/-- For a well-formed transaction, `TxIdDigester` computes each component digest the
    specification defines, one per bundle present. -/
theorem txIdDigests_eq (tx : TransactionData) (h : WellFormed tx) :
    tx.txIdDigests = some
      ⟨(Spec.headerDigest blake2b256 tx.toSpec.header).toList,
        tx.transparentBundle.map fun b => ⟨(Spec.prevoutsDigest blake2b256 b.toSpec).toList,
          (Spec.sequenceDigest blake2b256 b.toSpec).toList,
          (Spec.outputsDigest blake2b256 b.toSpec).toList⟩,
        tx.saplingBundle.map fun b =>
          (Spec.saplingDigest blake2b256 tx.toSpec.format b.toSpec).toList,
        tx.orchardBundle.map fun b => (Spec.actionsDigest blake2b256
          (orchardPersonalizations tx.version) tx.version.hasIronwood b.toSpec).toList,
        tx.ironwoodBundle.map fun b =>
          (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList⟩ := by
  have hf : tx.toSpec.format.IsV6 = tx.version.hasIronwood := by
    rcases h.version with hv | hv <;> simp [TransactionData.toSpec, hv, Spec.Format.IsV6,
      TxVersion.hasIronwood]
  simp only [TransactionData.txIdDigests, hashHeaderTxidData_eq,
    digestOrchard_eq _ _ h.orchardPool, digestIronwood_eq _ h.ironwoodPool, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  cases ht : tx.transparentBundle with
  | none =>
    cases hs : tx.saplingBundle with
    | none => simp
    | some s =>
      simp [hashSaplingTxidData_eq _ s (anchor_toSpec s (h.saplingAnchor s hs)) _ hf]
  | some b =>
    cases hs : tx.saplingBundle with
    | none => simp [transparentDigests_eq _ (h.outputScripts _ ht)]
    | some s =>
      simp [transparentDigests_eq _ (h.outputScripts _ ht),
        hashSaplingTxidData_eq _ s (anchor_toSpec s (h.saplingAnchor s hs)) _ hf]


/-- The empty Orchard digest in version 5, as the specification gives it. -/
theorem hashBundleTxidEmpty_orchard_v5 : Orchard.hashBundleTxidEmpty .orchard .v5 =
    some (.ok (Spec.actionsDigest blake2b256 Spec.orchardV5 false emptyOrchard).toList) :=
  hashBundleTxidEmpty_eq .orchard .v5 .orchardV5 rfl false

/-- The empty Orchard digest in version 6, as the specification gives it. -/
theorem hashBundleTxidEmpty_orchard_v6 : Orchard.hashBundleTxidEmpty .orchard .v6 =
    some (.ok (Spec.actionsDigest blake2b256 Spec.orchardV6 true emptyOrchard).toList) :=
  hashBundleTxidEmpty_eq .orchard .v6 .orchardV6 rfl true

/-- The empty Ironwood digest, as ZIP 229 gives it. -/
theorem hashBundleTxidEmpty_ironwood_v6 : Orchard.hashBundleTxidEmpty .ironwood .v6 =
    some (.ok (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true emptyOrchard).toList) :=
  hashBundleTxidEmpty_eq .ironwood .v6 .ironwoodV6 rfl true

/-- The transaction's transparent digest. -/
theorem transparentDigest_toSpec (tx : TransactionData) (h : WellFormed tx) :
    hashTransparentTxidData (tx.transparentBundle.map fun b =>
        ⟨(Spec.prevoutsDigest blake2b256 b.toSpec).toList,
          (Spec.sequenceDigest blake2b256 b.toSpec).toList,
          (Spec.outputsDigest blake2b256 b.toSpec).toList⟩) =
      some (Spec.transparentDigest blake2b256 tx.toSpec.transparent).toList := by
  cases ht : tx.transparentBundle with
  | none => simp [hashTransparentTxidData_none, TransactionData.toSpec, ht]
  | some b =>
    simp [hashTransparentTxidData_some b (h.transparentNonempty b ht), TransactionData.toSpec, ht]

/-- `to_hash` with both shielded digests present hashes the four digests in order. -/
theorem toHash_some (br : BitVec 32) (hd td s o : Blake2bHash) :
    toHash .v5 br hd td (some s) (some o) =
      some (blake2b256 (Spec.txHashPersonalization br) (hd ++ td ++ s ++ o)).toList := by
  simp only [toHash, hasher_eq, writeAll_absorbed, unwrap_ok, finalize_absorbed,
    txHashPersonalization_eq, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    List.nil_append, List.append_assoc]

/-- `to_hash` treats an absent Sapling digest as the empty one. -/
theorem toHash_none_sapling (v : TxVersion) (br : BitVec 32) (hd td : Blake2bHash)
    (o : Option Blake2bHash) (se : Blake2bHash) (hse : hashSaplingTxidEmpty = some se) :
    toHash v br hd td none o = toHash v br hd td (some se) o := by
  simp only [toHash, hse]
  rfl

/-- `to_hash` treats an absent Orchard digest as the empty one. -/
theorem toHash_none_orchard (br : BitVec 32) (hd td : Blake2bHash) (s : Option Blake2bHash)
    (oe : Blake2bHash) (hoe : Orchard.hashBundleTxidEmpty .orchard .v5 = some (.ok oe)) :
    toHash .v5 br hd td s none = toHash .v5 br hd td s (some oe) := by
  simp only [toHash, orchardCommitmentDomain, hoe]
  rfl

/-- `to_hash`, an absent Sapling or Orchard digest replaced by the empty one. The proof goes
    through `toHash_some`: one `simp` over the four cases makes a term the kernel times out on. -/
theorem toHash_eq (br : BitVec 32) (hd td : Blake2bHash) (s o : Option Blake2bHash)
    (se oe : Blake2bHash) (hse : hashSaplingTxidEmpty = some se)
    (hoe : Orchard.hashBundleTxidEmpty .orchard .v5 = some (.ok oe)) :
    toHash .v5 br hd td s o = some (blake2b256 (Spec.txHashPersonalization br)
      (hd ++ td ++ s.getD se ++ o.getD oe)).toList := by
  have h : toHash .v5 br hd td s o =
      toHash .v5 br hd td (some (s.getD se)) (some (o.getD oe)) := by
    cases s <;> cases o <;>
      simp only [Option.getD_some, Option.getD_none, toHash_none_sapling _ _ _ _ _ _ hse,
        toHash_none_orchard _ _ _ _ _ hoe]
  rw [h, toHash_some]

/-- `to_hash_v6` with all three shielded digests present hashes the five digests in order. -/
theorem toHashV6_some (br : BitVec 32) (hd td s o i : Blake2bHash) :
    toHashV6 br hd td (some s) (some o) (some i) =
      some (blake2b256 (Spec.txHashPersonalization br) (hd ++ td ++ s ++ o ++ i)).toList := by
  simp only [toHashV6, hasher_eq, writeAll_absorbed, unwrap_ok, finalize_absorbed,
    txHashPersonalization_eq, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    List.nil_append, List.append_assoc]

/-- `to_hash_v6` treats an absent Sapling digest as the empty one. -/
theorem toHashV6_none_sapling (br : BitVec 32) (hd td : Blake2bHash) (o i : Option Blake2bHash)
    (se : Blake2bHash) (hse : hashSaplingTxidEmpty = some se) :
    toHashV6 br hd td none o i = toHashV6 br hd td (some se) o i := by
  simp only [toHashV6, hse]
  rfl

/-- `to_hash_v6` treats an absent Orchard digest as the empty one. -/
theorem toHashV6_none_orchard (br : BitVec 32) (hd td : Blake2bHash) (s i : Option Blake2bHash)
    (oe : Blake2bHash) (hoe : Orchard.hashBundleTxidEmpty .orchard .v6 = some (.ok oe)) :
    toHashV6 br hd td s none i = toHashV6 br hd td s (some oe) i := by
  simp only [toHashV6, orchardCommitmentDomain, hoe]
  rfl

/-- `to_hash_v6` treats an absent Ironwood digest as the empty one. -/
theorem toHashV6_none_ironwood (br : BitVec 32) (hd td : Blake2bHash) (s o : Option Blake2bHash)
    (ie : Blake2bHash) (hie : Orchard.hashBundleTxidEmpty .ironwood .v6 = some (.ok ie)) :
    toHashV6 br hd td s o none = toHashV6 br hd td s o (some ie) := by
  simp only [toHashV6, ironwoodV6Domain, hie]
  rfl

/-- `to_hash_v6`, each absent digest replaced by the empty one. -/
theorem toHashV6_eq (br : BitVec 32) (hd td : Blake2bHash) (s o i : Option Blake2bHash)
    (se oe ie : Blake2bHash) (hse : hashSaplingTxidEmpty = some se)
    (hoe : Orchard.hashBundleTxidEmpty .orchard .v6 = some (.ok oe))
    (hie : Orchard.hashBundleTxidEmpty .ironwood .v6 = some (.ok ie)) :
    toHashV6 br hd td s o i = some (blake2b256 (Spec.txHashPersonalization br)
      (hd ++ td ++ s.getD se ++ o.getD oe ++ i.getD ie)).toList := by
  have h : toHashV6 br hd td s o i =
      toHashV6 br hd td (some (s.getD se)) (some (o.getD oe)) (some (i.getD ie)) := by
    cases s <;> cases o <;> cases i <;>
      simp only [Option.getD_some, Option.getD_none, toHashV6_none_sapling _ _ _ _ _ _ hse,
        toHashV6_none_orchard _ _ _ _ _ _ hoe, toHashV6_none_ironwood _ _ _ _ _ _ hie]
  rw [h, toHashV6_some]

/-- The Sapling digest `to_hash` hashes, the empty one standing in for an absent bundle, is
    the specification's Sapling digest of the transaction. -/
theorem saplingSlot (tx : TransactionData) :
    (tx.saplingBundle.map fun b =>
        (Spec.saplingDigest blake2b256 tx.toSpec.format b.toSpec).toList).getD
      (blake2b256 (personal "ZTxIdSaplingHash") []).toList =
    (Spec.saplingDigest blake2b256 tx.toSpec.format tx.toSpec.sapling).toList := by
  cases hb : tx.saplingBundle with
  | none => simp [TransactionData.toSpec, hb, saplingDigest_empty]
  | some b => simp [TransactionData.toSpec, hb]

/-- Likewise for the Orchard digest. -/
theorem orchardSlot (tx : TransactionData) (p : Spec.Personalizations) (v6 : Bool)
    (hp : orchardPersonalizations tx.version = p) (hv : tx.version.hasIronwood = v6) :
    (tx.orchardBundle.map fun b => (Spec.actionsDigest blake2b256
        (orchardPersonalizations tx.version) tx.version.hasIronwood b.toSpec).toList).getD
      (Spec.actionsDigest blake2b256 p v6 emptyOrchard).toList =
    (Spec.actionsDigest blake2b256 p v6 tx.toSpec.orchard).toList := by
  subst hp hv
  cases hb : tx.orchardBundle <;> simp [TransactionData.toSpec, hb]

/-- Likewise for the Ironwood digest. -/
theorem ironwoodSlot (ib : Option Orchard.Bundle) :
    (ib.map fun b => (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList).getD
      (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true emptyOrchard).toList =
    (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true
      ((ib.map Orchard.Bundle.toSpec).getD emptyOrchard)).toList := by
  cases ib <;> simp

/-- `to_txid` gives the specification's transaction identifier. -/
theorem txid_eq (tx : TransactionData) (h : WellFormed tx) :
    tx.txIdDigests.bind (toTxid tx.version tx.consensusBranchId) =
      some (some (tx.toSpec.txid blake2b256).toList) := by
  rw [txIdDigests_eq tx h, Option.bind_some]
  have htd := transparentDigest_toSpec tx h
  have hs := saplingSlot tx
  rcases h.version with hv | hv
  · have ho := orchardSlot tx Spec.orchardV5 false
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [toTxid, hv, TxVersion.hasIronwood, Bool.false_eq_true, ite_false, htd,
      toHash_eq _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq
        hashBundleTxidEmpty_orchard_v5, hs, ho]
    simp [Spec.Transaction.txid, Spec.txidDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]
  · have ho := orchardSlot tx Spec.orchardV6 true
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [toTxid, hv, TxVersion.hasIronwood, ite_true, htd,
      toHashV6_eq _ _ _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq hashBundleTxidEmpty_orchard_v6
        hashBundleTxidEmpty_ironwood_v6, hs, ho, ironwoodSlot]
    simp [Spec.Transaction.txid, Spec.txidDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]


/-! ## The authorizing data commitment -/

/-- `BlockTxCommitmentDigester::digest_transparent` is §A.1's digest of the `scriptSig`s. -/
theorem digestTransparent_eq (tx : TransactionData) (h : WellFormed tx) :
    BlockTxCommitmentDigester.digestTransparent tx.transparentBundle =
      some (Spec.transparentScriptsDigest blake2b256 tx.toSpec.scriptSigs).toList := by
  cases ht : tx.transparentBundle with
  | none =>
    simp [BlockTxCommitmentDigester.digestTransparent, hasher_eq, finalize_absorbed,
      Spec.transparentScriptsDigest, TransactionData.toSpec, ht]
  | some b =>
    simp only [BlockTxCommitmentDigester.digestTransparent, hasher_eq, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some]
    rw [forIn_absorbed b.vin _ _ (fun i : Transparent.TxIn => Spec.script i.scriptSig.code)
      (fun (a : Transparent.TxIn) r => unwrap (a.scriptSig.write r))
      (fun i hi _ => by simp [Script.write_absorbed _ _ _ (h.scriptSigs b ht i hi), unwrap_ok])]
    simp [finalize_absorbed, Spec.transparentScriptsDigest, TransactionData.toSpec, ht,
      List.flatMap_map]


/-- `BlockTxCommitmentDigester::digest_sapling` is §A.2's Sapling auth digest; in version 6,
    ZIP 229's, with the anchor when there is a spend. -/
theorem digestSapling_eq (tx : TransactionData) (h : WellFormed tx) :
    BlockTxCommitmentDigester.digestSapling tx.version tx.saplingBundle =
      some (Spec.saplingAuthDigest blake2b256 tx.toSpec.format tx.toSpec.sapling).toList := by
  cases hb : tx.saplingBundle with
  | none =>
    rcases h.version with hv | hv <;>
      simp [BlockTxCommitmentDigester.digestSapling, hasher_eq, finalize_absorbed,
        Spec.saplingAuthDigest, TransactionData.toSpec, hb, hv, emptySapling, Spec.Format.IsV6,
        saplingAuthPersonalization]
  | some b =>
    simp only [BlockTxCommitmentDigester.digestSapling, hasher_eq, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some]
    rw [forIn_absorbed b.shieldedSpends _ _ (fun s : Sapling.SpendDescription => s.zkproof.toList)
      (fun (a : Sapling.SpendDescription) r => unwrap (r.writeAll a.zkproof.toList))
      (fun _ _ _ => by simp [writeAll_absorbed, unwrap_ok]), Option.bind_some]
    rw [forIn_absorbed b.shieldedSpends _ _
      (fun s : Sapling.SpendDescription => s.spendAuthSig.toList)
      (fun (a : Sapling.SpendDescription) r => unwrap (r.writeAll a.spendAuthSig.toList))
      (fun _ _ _ => by simp [writeAll_absorbed, unwrap_ok]), Option.bind_some]
    rw [forIn_absorbed b.shieldedOutputs _ _
      (fun o : Sapling.OutputDescription => o.zkproof.toList)
      (fun (a : Sapling.OutputDescription) r => unwrap (r.writeAll a.zkproof.toList))
      (fun _ _ _ => by simp [writeAll_absorbed, unwrap_ok]), Option.bind_some]
    rcases h.version with hv | hv <;> cases hs : b.shieldedSpends <;>
      (try have ho : b.shieldedOutputs ≠ [] := by simpa [hs] using h.saplingNonempty b hb) <;>
      simp [writeAll_absorbed, unwrap_ok, finalize_absorbed, Spec.saplingAuthDigest,
        TransactionData.toSpec, *, Sapling.Bundle.toSpec, List.flatMap_map,
        Spec.Format.IsV6, saplingAuthPersonalization, saplingAuthIncludesAnchor]


/-- `orchard`'s version 5 Orchard personalizations are the specification's. -/
theorem personalizations_orchardV5 :
    Orchard.BundleCommitmentFormat.orchardV5.personalizations.toSpec = Spec.orchardV5 := rfl

/-- `orchard`'s version 6 Orchard personalizations are ZIP 229's. -/
theorem personalizations_orchardV6 :
    Orchard.BundleCommitmentFormat.orchardV6.personalizations.toSpec = Spec.orchardV6 := rfl

/-- `orchard`'s Ironwood personalizations are ZIP 229's. -/
theorem personalizations_ironwoodV6 :
    Orchard.BundleCommitmentFormat.ironwoodV6.personalizations.toSpec = Spec.ironwoodV6 := rfl

/-- `hash_bundle_auth_data` is §A.3's auth digest under the bundle's commitment format: its
    personalization, and the anchor exactly when the format includes it. -/
theorem hashBundleAuthData_eq (b : Orchard.Bundle) (v : Orchard.TxVersion)
    (format : Orchard.BundleCommitmentFormat) (hf : b.valuePool.commitmentFormat v = .ok format) :
    Orchard.hashBundleAuthData b v = some (.ok (Spec.actionsAuthDigest blake2b256
      format.personalizations.toSpec format.includesAnchorInAuthorizingDigest
      b.toSpec).toList) := by
  simp only [Orchard.hashBundleAuthData, hf, orchard_absorbed, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, update_absorbed]
  rw [forIn_yield _ _ _ (fun (a : Orchard.Action) st => Orchard.update st a.authorization.toList)
    (fun _ _ _ => rfl), foldl_update_absorbed]
  cases format <;>
    simp [Orchard.BundleCommitmentFormat.includesAnchorInAuthorizingDigest, update_absorbed,
      finalize_state_absorbed, Spec.actionsAuthDigest, Orchard.Bundle.toSpec,
      Orchard.NonEmpty.toList, List.flatMap_map, Orchard.Personalizations.toSpec]

/-- `hash_bundle_auth_empty` is the specification's auth digest of no actions under the
    format's personalization. -/
theorem hashBundleAuthEmpty_eq (vp : Orchard.ValuePool) (v : Orchard.TxVersion)
    (format : Orchard.BundleCommitmentFormat) (hf : vp.commitmentFormat v = .ok format)
    (anchor : Bool) :
    Orchard.hashBundleAuthEmpty vp v = some (.ok (Spec.actionsAuthDigest blake2b256
      format.personalizations.toSpec anchor emptyOrchard).toList) := by
  simp [Orchard.hashBundleAuthEmpty, hf, orchard_absorbed, finalize_state_absorbed,
    Spec.actionsAuthDigest, emptyOrchard, Orchard.Personalizations.toSpec]

/-- `BlockTxCommitmentDigester::digest_orchard` is the specification's Orchard auth digest of
    the transaction, for its version. -/
theorem digestOrchardAuth_eq (tx : TransactionData) (h : WellFormed tx) :
    BlockTxCommitmentDigester.digestOrchard tx.version tx.orchardBundle =
      some (if tx.toSpec.format.IsV6 then
        Spec.actionsAuthDigest blake2b256 Spec.orchardV6 true tx.toSpec.orchard
      else Spec.actionsAuthDigest blake2b256 Spec.orchardV5 false tx.toSpec.orchard).toList := by
  cases ho : tx.orchardBundle with
  | none =>
    rcases h.version with hv | hv <;>
      simp [BlockTxCommitmentDigester.digestOrchard, orchardCommitmentDomain, hv, unwrap_ok,
        hashBundleAuthEmpty_eq .orchard .v5 .orchardV5 rfl false,
        hashBundleAuthEmpty_eq .orchard .v6 .orchardV6 rfl true, TransactionData.toSpec, ho,
        Spec.Format.IsV6, personalizations_orchardV5, personalizations_orchardV6]
  | some b =>
    have hp := h.orchardPool b ho
    rcases h.version with hv | hv <;>
      simp [BlockTxCommitmentDigester.digestOrchard, orchardCommitmentDomain, hv, unwrap_ok,
        hashBundleAuthData_eq b .v5 .orchardV5 (by simp [hp, Orchard.ValuePool.commitmentFormat]),
        hashBundleAuthData_eq b .v6 .orchardV6 (by simp [hp, Orchard.ValuePool.commitmentFormat]),
        TransactionData.toSpec, ho, Spec.Format.IsV6, personalizations_orchardV5,
        personalizations_orchardV6,
        Orchard.BundleCommitmentFormat.includesAnchorInAuthorizingDigest]

/-- `BlockTxCommitmentDigester::digest_ironwood` is ZIP 229's Ironwood auth digest. -/
theorem digestIronwoodAuth_eq (tx : TransactionData) (h : WellFormed tx) :
    BlockTxCommitmentDigester.digestIronwood tx.ironwoodBundle =
      some (Spec.actionsAuthDigest blake2b256 Spec.ironwoodV6 true
        ((tx.ironwoodBundle.map Orchard.Bundle.toSpec).getD emptyOrchard)).toList := by
  cases hi : tx.ironwoodBundle with
  | none =>
    simp [BlockTxCommitmentDigester.digestIronwood, ironwoodV6Domain, unwrap_ok,
      hashBundleAuthEmpty_eq .ironwood .v6 .ironwoodV6 rfl true, personalizations_ironwoodV6]
  | some b =>
    simp [BlockTxCommitmentDigester.digestIronwood, ironwoodV6Domain, unwrap_ok,
      hashBundleAuthData_eq b .v6 .ironwoodV6
        (by simp [h.ironwoodPool b hi, Orchard.ValuePool.commitmentFormat]),
      personalizations_ironwoodV6, Orchard.BundleCommitmentFormat.includesAnchorInAuthorizingDigest]

/-- `auth_commitment` gives the specification's authorizing data commitment. -/
theorem authCommitment_eq (tx : TransactionData) (h : WellFormed tx) :
    tx.authCommitment = some (tx.toSpec.authDigest blake2b256).toList := by
  simp only [TransactionData.authCommitment, digestTransparent_eq tx h, digestSapling_eq tx h,
    digestOrchardAuth_eq tx h, digestIronwoodAuth_eq tx h, Option.bind_eq_bind, Option.bind_some,
    authPersonalization_eq, hasher_eq, writeAll_absorbed, unwrap_ok, Option.pure_def]
  rcases h.version with hv | hv <;>
    simp [hv, TxVersion.hasIronwood, finalize_absorbed, Spec.Transaction.authDigest, Spec.node,
      TransactionData.toSpec, Spec.Format.IsV6]


/-! ## Signature hashes -/

/-- On a byte `SighashType::parse` accepts, the masks `transparent_sig_digest` tests give the
    specification's hash type. -/
theorem flags_of_ofByte? (b : Byte) (ht : Spec.HashType) (hb : Spec.HashType.ofByte? b = some ht) :
    (b &&& Transparent.SIGHASH_ANYONECANPAY != 0) = ht.anyoneCanPay ∧
      (b &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_SINGLE) = (ht.base == .single) ∧
      (b &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_NONE) = (ht.base == .none) := by
  revert ht
  revert b
  decide

/-- `SighashType::parse` accepts exactly the bytes that encode hash types. -/
theorem parse_isSome (b : Byte) :
    (Transparent.SighashType.parse b).isSome = (Spec.HashType.ofByte? b).isSome := by
  revert b
  decide

/-- `Bundle::is_coinbase` decides the specification's coinbase rule (§3.11). -/
theorem isCoinbase_toSpec (b : Transparent.Bundle) :
    b.toSpec.IsCoinbase ↔ b.isCoinbase = true := by
  rcases hv : b.vin with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;>
    simp [Spec.Transparent.IsCoinbase, Transparent.Bundle.toSpec, Transparent.Bundle.isCoinbase,
      Transparent.Bundle.txinToSpec, hv, Spec.OutPoint.IsNull, Transparent.OutPoint.isNull]

/-- The authorizing context has one entry per input, and no `scriptPubKey` it gives exceeds
    `MAX_COMPACT_SIZE`. -/
structure ContextFits (b : Transparent.Bundle) : Prop where
  amounts : b.authorization.inputAmounts.length = b.vin.length
  scripts : b.authorization.inputScriptpubkeys.length = b.vin.length
  scriptLength : ∀ s ∈ b.authorization.inputScriptpubkeys, s.code.length ≤ MAX_COMPACT_SIZE

/-- With one amount per input, the specification's spent values are the authorizing
    context's amounts. -/
theorem toSpec_amounts (b : Transparent.Bundle) (hc : ContextFits b) :
    b.toSpec.vin.map (·.spent.value) = b.authorization.inputAmounts := by
  apply List.ext_getElem (by simp [Transparent.Bundle.toSpec, hc.amounts])
  intro i h₁ h₂
  simp [Transparent.Bundle.toSpec, Transparent.Bundle.txinToSpec, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h₂]

/-- With one `scriptPubKey` per input, the specification's spent scripts are the authorizing
    context's. -/
theorem toSpec_scripts (b : Transparent.Bundle) (hc : ContextFits b) :
    b.toSpec.vin.map (·.spent.scriptPubKey) = b.authorization.inputScriptpubkeys.map (·.code) := by
  apply List.ext_getElem (by simp [Transparent.Bundle.toSpec, hc.scripts])
  intro i h₁ h₂
  simp [Transparent.Bundle.toSpec, Transparent.Bundle.txinToSpec, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using h₂)]


/-- `TransparentInputsDigests::new` gives §S.2c's and §S.2d's digests without
    `ANYONECANPAY`. -/
theorem inputsDigests_new_eq (b : Transparent.Bundle) (hc : ContextFits b) :
    TransparentInputsDigests.new b = some
      ⟨(blake2b256 (personal "ZTxTrAmountsHash")
          (b.toSpec.vin.flatMap (Spec.i64 ·.spent.value))).toList,
        (blake2b256 (personal "ZTxTrScriptsHash")
          (b.toSpec.vin.flatMap (Spec.script ·.spent.scriptPubKey))).toList⟩ := by
  have ha : b.toSpec.vin.flatMap (Spec.i64 ·.spent.value) =
      b.authorization.inputAmounts.flatMap Spec.i64 := by
    rw [← toSpec_amounts b hc, List.flatMap_map]
  have hs : b.toSpec.vin.flatMap (Spec.script ·.spent.scriptPubKey) =
      b.authorization.inputScriptpubkeys.flatMap (Spec.script ·.code) := by
    have := congrArg (List.flatMap Spec.script) (toSpec_scripts b hc)
    simpa [List.flatMap_map] using this
  simp only [TransparentInputsDigests.new, hasher_eq, Option.bind_eq_bind, Option.bind_some,
    Array.write, Option.pure_def]
  rw [foldlM_absorbed _ _ _ Spec.i64 _ fun a _ y => by rw [writeAll_absorbed, toLeBytes_i64],
    foldlM_absorbed _ _ _ (Spec.script ·.code) _
      fun s hs y => Script.write_absorbed s _ _ (hc.scriptLength s hs)]
  simp [unwrap_ok, finalize_absorbed, ha, hs]

/-- The Rust signable input is the specification's: a shielded one, or the transparent input
    at the same index, with a hash type `SighashType::parse` accepts and the value and
    `scriptPubKey` its authorizing context gives. -/
inductive InputRel (b : Transparent.Bundle) : SignableInput → Spec.SignableInput b.toSpec → Prop
  | shielded : InputRel b .shielded .shielded
  | transparent (input : Transparent.SignableInput) (ht : Spec.HashType)
      (i : Fin b.toSpec.vin.length) (hh : Spec.HashType.ofByte? input.hashType.byte = some ht)
      (hi : input.index = i.val) (hv : input.value = b.authorization.inputAmounts.getD i 0)
      (hs : input.scriptPubkey = b.authorization.inputScriptpubkeys.getD i ⟨[]⟩) :
      InputRel b (.transparent input) (.transparent ht i)


/-! The kernel times out on proofs that rewrite `bind` into `Option.bind` across a long `do`
    block, so the signature hash proofs stay with `pure` and `pure_bind`. -/

/-- `hasher_eq` in the `pure` form. -/
theorem hasher_pure (p : Bytes 16) : hasher p = pure (absorbed p []) := hasher_eq p

/-- `unwrap_ok` in the `pure` form. -/
theorem unwrap_pure {ε α : Type} (a : α) : unwrap (Except.ok a : Except ε α) = pure a := rfl

/-- `some` is `pure`, to turn a step lemma's result into the `pure` form. -/
theorem some_eq_pure {α : Type} (a : α) : (some a : Option α) = pure a := rfl

/-- The specification's byte for `SIGHASH_ALL` is the Rust's. -/
theorem toByte_all : Spec.HashType.toByte ⟨.all, false⟩ = Transparent.SIGHASH_ALL := by decide

/-- `SIGHASH_ALL`, a shielded input's hash type, sets none of the flags. -/
theorem all_flags :
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_ANYONECANPAY != 0) = false ∧
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_SINGLE) = false ∧
    (Transparent.SIGHASH_ALL &&& Transparent.SIGHASH_MASK == Transparent.SIGHASH_NONE) = false :=
  by decide

/-- The base comparisons the specification's §S.2f evaluates, for `simp`. -/
theorem base_beq :
    (Spec.Base.all == Spec.Base.single) = false ∧ (Spec.Base.all == Spec.Base.none) = false ∧
    (Spec.Base.none == Spec.Base.single) = false ∧ (Spec.Base.none == Spec.Base.none) = true ∧
    (Spec.Base.single == Spec.Base.single) = true ∧ (Spec.Base.single == Spec.Base.none) = false :=
  by decide

/-- The input digests `transparent_sig_digest` is given: none, or those `new` computes. -/
def InputsDigestsFit (b : Transparent.Bundle) (d : Option TransparentInputsDigests) : Prop :=
  d = none ∨ d = some ⟨(blake2b256 (personal "ZTxTrAmountsHash")
      (b.toSpec.vin.flatMap (Spec.i64 ·.spent.value))).toList,
    (blake2b256 (personal "ZTxTrScriptsHash")
      (b.toSpec.vin.flatMap (Spec.script ·.spent.scriptPubKey))).toList⟩

/-- The transparent digests a bundle's identifier commits to. -/
def txidDigestsOf (b : Transparent.Bundle) : TransparentDigests :=
  ⟨(Spec.prevoutsDigest blake2b256 b.toSpec).toList,
    (Spec.sequenceDigest blake2b256 b.toSpec).toList,
    (Spec.outputsDigest blake2b256 b.toSpec).toList⟩

/-- §S.2's preimage, for a hash type and the last two digests. -/
def sigPreimage (b : Transparent.Bundle) (ht : Spec.HashType) (outputs txin : Spec.Digest) :
    List Byte :=
  ht.toByte :: [Spec.prevoutsSigDigest blake2b256 b.toSpec ht,
    Spec.amountsSigDigest blake2b256 b.toSpec ht,
    Spec.scriptPubKeysSigDigest blake2b256 b.toSpec ht,
    Spec.sequenceSigDigest blake2b256 b.toSpec ht, outputs, txin].flatMap (·.toList)

/-- The fields of `txidDigestsOf`, as `rfl` lemmas: unfolding the definition instead makes the
    signature hash proofs time out. -/
theorem txidDigestsOf_fields (b : Transparent.Bundle) :
    (txidDigestsOf b).prevoutsDigest = (Spec.prevoutsDigest blake2b256 b.toSpec).toList ∧
    (txidDigestsOf b).sequenceDigest = (Spec.sequenceDigest blake2b256 b.toSpec).toList ∧
    (txidDigestsOf b).outputsDigest = (Spec.outputsDigest blake2b256 b.toSpec).toList :=
  ⟨rfl, rfl, rfl⟩

/-- For a non-coinbase bundle with inputs, `transparent_sig_digest` of a shielded input is
    §S.2's digest under `SIGHASH_ALL`, with §S.2g's empty input digest. -/
theorem transparentSigDigest_shielded (b : Transparent.Bundle) (hc : ContextFits b)
    (hcb : ¬(b.isCoinbase || b.vin.isEmpty) = true) (d : Option TransparentInputsDigests)
    (hd : InputsDigestsFit b d) :
    transparentSigDigest (some (b, txidDigestsOf b)) d .shielded =
      some (blake2b256 (personal "ZTxIdTranspaHash") (sigPreimage b ⟨.all, false⟩
        (Spec.outputsSigDigest blake2b256 (t := b.toSpec) .shielded)
        (Spec.txinSigDigest blake2b256 (t := b.toSpec) .shielded))).toList := by
  unfold InputsDigestsFit at hd
  rcases hd with h | h <;> subst h <;> unfold transparentSigDigest <;>
    simp only [(txidDigestsOf_fields b).1, (txidDigestsOf_fields b).2.1,
      (txidDigestsOf_fields b).2.2, hcb, Bool.false_eq_true, ite_false] <;>
    simp only [SignableInput.hashType, all_flags, Bool.false_eq_true, ite_false,
      Spec.txinSigDigest] <;>
    simp only [hasher_pure, pure_bind, writeAll_absorbed, unwrap_pure, finalize_absorbed,
      inputsDigests_new_eq b hc, some_eq_pure] <;>
    simp only [sigPreimage, Spec.prevoutsSigDigest, Spec.amountsSigDigest,
      Spec.scriptPubKeysSigDigest, Spec.sequenceSigDigest, Spec.outputsSigDigest,
      Spec.SignableInput.hashType, toByte_all, Bool.false_eq_true, ite_false, List.flatMap_cons,
      List.flatMap_nil, List.append_assoc, List.nil_append, List.cons_append, List.append_nil]

/-- For a non-coinbase bundle with inputs, `transparent_sig_digest` of a transparent input
    with a defined hash type, and its coin from the authorizing context, is §S.2's digest. -/
theorem transparentSigDigest_transparent (b : Transparent.Bundle)
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) (hc : ContextFits b)
    (hcb : ¬(b.isCoinbase || b.vin.isEmpty) = true) (d : Option TransparentInputsDigests)
    (hd : InputsDigestsFit b d) (input : Transparent.SignableInput) (ht : Spec.HashType)
    (i : Fin b.toSpec.vin.length) (hh : Spec.HashType.ofByte? input.hashType.byte = some ht)
    (hi : input.index = i.val) (hv : input.value = b.authorization.inputAmounts.getD i 0)
    (hs : input.scriptPubkey = b.authorization.inputScriptpubkeys.getD i ⟨[]⟩) :
    transparentSigDigest (some (b, txidDigestsOf b)) d (.transparent input) =
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
  have hon : transparentOutputsHash [] =
      some (blake2b256 (personal "ZTxIdOutputsHash") []).toList := by
    simpa using transparentOutputsHash_eq [] (by simp)
  have hos : ∀ (h : i.val < b.vout.length), transparentOutputsHash [b.vout[i.val]] =
      some (blake2b256 (personal "ZTxIdOutputsHash")
        (Spec.i64 b.vout[i.val].value ++ Spec.script b.vout[i.val].scriptPubkey.code)).toList :=
    fun h => by simpa using transparentOutputsHash_eq _ (hko h)
  have hpn : transparentPrevoutHash [] =
      some (blake2b256 (personal "ZTxIdPrevoutHash") []).toList := by
    simpa using transparentPrevoutHash_eq []
  have hsn : transparentSequenceHash [] =
      some (blake2b256 (personal "ZTxIdSequencHash") []).toList := by
    simpa using transparentSequenceHash_eq []
  have hvout : b.toSpec.vout = b.vout.map fun o => ⟨o.value, o.scriptPubkey.code⟩ := rfl
  obtain ⟨base, acp⟩ := ht
  rcases hd with rfl | rfl <;> cases base <;> cases acp <;>
    simp (config := {decide := true}) only [] at hacp hsingle hnone <;>
    unfold transparentSigDigest <;>
    simp only [(txidDigestsOf_fields b).1, (txidDigestsOf_fields b).2.1,
      (txidDigestsOf_fields b).2.2, hcb, Bool.false_eq_true, ite_false, ite_true,
      SignableInput.hashType, Transparent.SighashType.encode, hacp, hsingle, hnone, hi,
      base_beq] <;>
    (try by_cases hio : i.val < b.vout.length) <;>
    (try have hio' : b.vout.length ≤ i.val := by omega) <;>
    simp only [hasher_pure, pure_bind, writeAll_absorbed, unwrap_pure, finalize_absorbed,
      OutPoint.write_absorbed, Script.write_absorbed _ _ _ hsb, toLeBytes_i64, toLeBytes_u32,
      inputsDigests_new_eq b hc, some_eq_pure, hvin, hon, hpn, hsn, hio, hos,
      List.getElem?_eq_getElem, ite_true, ite_false] <;>
    simp only [sigPreimage, Spec.prevoutsSigDigest, Spec.amountsSigDigest,
      Spec.scriptPubKeysSigDigest, Spec.sequenceSigDigest, Spec.outputsSigDigest,
      Spec.txinSigDigest, Spec.SignableInput.hashType, Transparent.Bundle.txinToSpec,
      Spec.OutPoint.encode, Spec.TxOut.encode, List.getElem?_map, List.getElem?_eq_getElem,
      some_eq_pure, Option.map_none, List.getElem?_eq_none, *, ite_true, ite_false,
      Bool.false_eq_true, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.nil_append,
      List.cons_append, List.append_nil] <;>
    rfl


/-- `transparent_sig_digest` gives §S.2's transparent signature digest. -/
theorem transparentSigDigest_eq (b : Transparent.Bundle) (hne : b.vin ≠ [] ∨ b.vout ≠ [])
    (hk : ∀ o ∈ b.vout, o.scriptPubkey.code.length ≤ MAX_COMPACT_SIZE) (hc : ContextFits b)
    (d : Option TransparentInputsDigests) (hd : InputsDigestsFit b d)
    (input : SignableInput) (sinput : Spec.SignableInput b.toSpec) (hr : InputRel b input sinput) :
    transparentSigDigest (some (b, txidDigestsOf b)) d input =
      some (Spec.transparentSigDigest blake2b256 sinput).toList := by
  have hvin : b.toSpec.vin = [] ↔ b.vin = [] := by simp [Transparent.Bundle.toSpec]
  by_cases hcb : (b.isCoinbase || b.vin.isEmpty) = true
  · have hcb' : b.toSpec.IsCoinbase ∨ b.toSpec.vin = [] := by
      simpa [isCoinbase_toSpec, hvin, List.isEmpty_iff] using hcb
    simp only [transparentSigDigest, hcb, ite_true, Spec.transparentSigDigest, hcb']
    exact hashTransparentTxidData_some b hne
  · have hcb' : ¬(b.toSpec.IsCoinbase ∨ b.toSpec.vin = []) := by
      simpa [isCoinbase_toSpec, hvin, List.isEmpty_iff] using hcb
    rw [Spec.transparentSigDigest, ite_eq_right hcb']
    rcases hr with _ | ⟨input, ht, i, hh, hi, hv, hs⟩
    · exact transparentSigDigest_shielded b hc hcb d hd
    · exact transparentSigDigest_transparent b hk hc hcb d hd input ht i hh hi hv hs

/-! ## The signature hash -/

/-- The ZIP 244 digests of a well-formed transaction, as the specification's. -/
def zip244DigestsOf (tx : TransactionData) : Zip244Digests :=
  ⟨(Spec.headerDigest blake2b256 tx.toSpec.header).toList, tx.transparentBundle.map txidDigestsOf,
    tx.saplingBundle.map fun b => (Spec.saplingDigest blake2b256 tx.toSpec.format b.toSpec).toList,
    tx.orchardBundle.map fun b => (Spec.actionsDigest blake2b256
      (orchardPersonalizations tx.version) tx.version.hasIronwood b.toSpec).toList,
    tx.ironwoodBundle.map fun b =>
      (Spec.actionsDigest blake2b256 Spec.ironwoodV6 true b.toSpec).toList⟩

/-- The input digests `TransparentInputsDigests::for_bundle` precomputes are ones
    `transparent_sig_digest` accepts. -/
theorem forBundle_fits (b : Transparent.Bundle) (hc : ContextFits b)
    (d : Option TransparentInputsDigests)
    (hd : TransparentInputsDigests.forBundle b = some d) : InputsDigestsFit b d := by
  unfold TransparentInputsDigests.forBundle at hd
  split at hd
  · right
    simp only [inputsDigests_new_eq b hc, Option.map_eq_map, Option.map_some] at hd
    exact (Option.some.inj hd).symm
  · left
    exact (Option.some.inj hd).symm

/-- `PrecomputedSighashData::new_zip244` computes the specification's digests. -/
theorem newZip244_eq (tx : TransactionData) (h : WellFormed tx)
    (hc : ∀ b, tx.transparentBundle = some b → ContextFits b) :
    ∃ d, PrecomputedSighashData.newZip244 tx = some (some ⟨tx, zip244DigestsOf tx, d⟩) ∧
      ∀ b, tx.transparentBundle = some b → InputsDigestsFit b d := by
  have hd := txIdDigests_eq tx h
  cases ht : tx.transparentBundle with
  | none =>
    refine ⟨none, ?_, fun b hb => by simp at hb⟩
    rcases h.version with hv | hv <;>
      simp [PrecomputedSighashData.newZip244, hv, hd, ht, zip244DigestsOf]
  | some b =>
    obtain ⟨d, hf⟩ : ∃ d, TransparentInputsDigests.forBundle b = some d := by
      unfold TransparentInputsDigests.forBundle
      split <;> simp [inputsDigests_new_eq b (hc b ht)]
    refine ⟨d, ?_, fun b' hb' => ?_⟩
    · rcases h.version with hv | hv <;>
        simp [PrecomputedSighashData.newZip244, hv, hd, ht, hf, zip244DigestsOf, txidDigestsOf]
    · obtain rfl := Option.some.inj hb'
      exact forBundle_fits b (hc b ht) d hf


/-- `signature_hash` gives the specification's signature digest. -/
theorem signatureHash_eq (tx : TransactionData) (h : WellFormed tx) (b : Transparent.Bundle)
    (hb : tx.transparentBundle = some b) (hc : ContextFits b) (d : Option TransparentInputsDigests)
    (hd : InputsDigestsFit b d) (input : SignableInput) (sinput : Spec.SignableInput b.toSpec)
    (hr : InputRel b input sinput) :
    (⟨tx, zip244DigestsOf tx, d⟩ : PrecomputedSighashData).signatureHash input =
      some (Spec.signatureDigest blake2b256 (tx.toSpec.version blake2b256) tx.consensusBranchId
        (Spec.headerDigest blake2b256 tx.toSpec.header)
        (Spec.saplingDigest blake2b256 tx.toSpec.format tx.toSpec.sapling)
        (tx.toSpec.orchardDigest blake2b256) sinput).toList := by
  have hts := transparentSigDigest_eq b (h.transparentNonempty b hb) (h.outputScripts b hb) hc d hd
    input sinput hr
  have hs := saplingSlot tx
  rcases h.version with hv | hv
  · have ho := orchardSlot tx Spec.orchardV5 false
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [PrecomputedSighashData.signatureHash, v5SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, Bool.false_eq_true, ite_false, Option.map_some, Option.isSome_some,
      zipOption, guard, ite_true]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHash_eq _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq
      hashBundleTxidEmpty_orchard_v5, hs, ho]
    simp [Spec.signatureDigest, Spec.Transaction.version, Spec.Transaction.orchardDigest,
      TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]
  · have ho := orchardSlot tx Spec.orchardV6 true
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [PrecomputedSighashData.signatureHash, v6SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, ite_true, Option.map_some, Option.isSome_some, zipOption, guard]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHashV6_eq _ _ _ _ _ _ _ _ _
      hashSaplingTxidEmpty_eq hashBundleTxidEmpty_orchard_v6 hashBundleTxidEmpty_ironwood_v6, hs,
      ho, ironwoodSlot]
    simp [Spec.signatureDigest, Spec.Transaction.version, Spec.Transaction.orchardDigest,
      TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]


/-- Without a transparent bundle, `signature_hash` gives the shielded signature digest, for a
    transparent input too. -/
theorem signatureHash_noTransparent (tx : TransactionData) (h : WellFormed tx)
    (hb : tx.transparentBundle = none) (input : SignableInput) :
    (⟨tx, zip244DigestsOf tx, none⟩ : PrecomputedSighashData).signatureHash input =
      some (tx.toSpec.signatureDigest blake2b256 .shielded).toList := by
  have hts : transparentSigDigest none none input =
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
    simp only [PrecomputedSighashData.signatureHash, v5SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, Bool.false_eq_true, ite_false, Option.map_none, Option.isSome_none,
      zipOption, guard, ite_true]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHash_eq _ _ _ _ _ _ _ hashSaplingTxidEmpty_eq
      hashBundleTxidEmpty_orchard_v5, hs, ho]
    simp [Spec.Transaction.signatureDigest, Spec.signatureDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]
  · have ho := orchardSlot tx Spec.orchardV6 true
      (by simp [orchardPersonalizations, hv, TxVersion.hasIronwood])
      (by simp [hv, TxVersion.hasIronwood])
    simp only [hv, TxVersion.hasIronwood] at ho
    simp only [PrecomputedSighashData.signatureHash, v6SignatureHash, zip244DigestsOf, hv, hb,
      TxVersion.hasIronwood, ite_true, Option.map_none, Option.isSome_none, zipOption, guard]
    rw [hts, some_eq_pure, pure_bind, pure_bind, toHashV6_eq _ _ _ _ _ _ _ _ _
      hashSaplingTxidEmpty_eq hashBundleTxidEmpty_orchard_v6 hashBundleTxidEmpty_ironwood_v6, hs,
      ho, ironwoodSlot]
    simp [Spec.Transaction.signatureDigest, Spec.signatureDigest, Spec.Transaction.version,
      Spec.Transaction.orchardDigest, TransactionData.toSpec, hv, Spec.Format.IsV6, Spec.node]

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.txid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms txid_eq

/--
info: 'ZcashSighash.Verifier.authCommitment_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms authCommitment_eq

/--
info: 'ZcashSighash.Verifier.signatureHash_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signatureHash_eq

end ZcashSighash.Verifier
