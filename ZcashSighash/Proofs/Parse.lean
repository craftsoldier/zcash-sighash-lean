/-
What Zakura's transparent parser guarantees (G3): every input and output it parses meets the
hypotheses of the native digest theorems (`Proofs/Native.lean`). Their scripts fit in a protocol
message, no input that spends a coin has the null outpoint, and each coinbase input's `scriptSig`
is the one `coinbase_script` rebuilds.
-/
module

public import ZcashSighash.Proofs.Native
public import ZcashSighash.Verifier.Parse

@[expose] public section

namespace ZcashSighash.Verifier.Native

open Spec (Byte Bytes)

/-- A parse that succeeds succeeds at each step. -/
theorem Parser.bind_eq_some {α β : Type} {x : Parser α} {f : α → Parser β} {s : List Byte}
    {r : β × List Byte} :
    (x >>= f) s = some r ↔ ∃ a s₁, x s = some (a, s₁) ∧ f a s₁ = some r := by
  simp only [bind, StateT.bind, Option.bind_eq_some_iff, Prod.exists]

/-- An error fails whatever follows it. -/
@[simp] theorem fail_apply {α : Type} (s : List Byte) : (fail : Parser α) s = none := rfl

/-- An error fails whatever is made of its result. -/
@[simp] theorem map_fail {α β : Type} (f : α → β) (s : List Byte) :
    (f <$> (fail : Parser α)) s = none := rfl

/-- An error fails whatever follows it. -/
@[simp] theorem bind_fail {α β : Type} (f : α → Parser β) (s : List Byte) :
    ((fail : Parser α) >>= f) s = none := rfl

/-- A value is returned without reading. -/
@[simp] theorem pure_apply {α : Type} (a : α) (s : List Byte) :
    (pure a : Parser α) s = some (a, s) := rfl

/-- `read_exact` reads exactly the bytes asked for. -/
theorem readBytes_length {n : ℕ} {s s' bytes : List Byte}
    (h : readBytes n s = some (bytes, s')) : bytes.length = n := by
  unfold readBytes at h
  split_ifs at h with hn
  cases h
  simp
  omega

/-- A `CompactSizeMessage` is at most `MAX_PROTOCOL_MESSAGE_LEN`. -/
theorem readCompactSizeMessage_le {n : ℕ} {s s' : List Byte}
    (h : readCompactSizeMessage s = some (n, s')) : n ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  obtain ⟨size, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  by_cases h1 : 4294967296 ≤ size <;> by_cases h2 : size > MAX_PROTOCOL_MESSAGE_LEN <;>
    simp [h1, h2] at h
  omega

/-- A byte vector Zakura parses fits in a protocol message. -/
theorem readByteVec_le {s s' bytes : List Byte} (h : readByteVec s = some (bytes, s')) :
    bytes.length ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  obtain ⟨len, s₁, hl, hb⟩ := Parser.bind_eq_some.mp h
  rw [readBytes_length hb]
  exact readCompactSizeMessage_le hl

/-- An output's script fits in a protocol message. -/
theorem readOutput_le {s s' : List Byte} {o : Output} (h : readOutput s = some (o, s')) :
    o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  obtain ⟨v, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨ls, s₂, hl, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact readByteVec_le hl

/-- An `Option` lifted into the parser reads nothing. -/
@[simp] theorem liftM_apply {α : Type} (o : Option α) (s : List Byte) :
    (liftM o : Parser α) s = o.map (·, s) := by
  cases o <;> rfl

/-- `push_num(0)` is `OP_0`, the byte 0. -/
theorem pushNum_zero : (PushNum.pushNum 0).toBytes = [0] := by decide

/-- What `parse_coinbase_height` returns rebuilds the `scriptSig`: `push_num` of the height,
    then the data. A height of 0 never comes from it. -/
theorem parseCoinbaseHeight_spec {scriptSig data : List Byte} {height : BitVec 32}
    (h : parseCoinbaseHeight scriptSig = some (height, data)) :
    CoinbaseScript.zakura.pushNum height ++ data = scriptSig ∧ height ≠ 0 := by
  unfold parseCoinbaseHeight at h
  obtain ⟨⟨n, len⟩, hsel, h⟩ := Option.bind_eq_some_iff.mp h
  -- The prefix is one byte, or a length byte and that many bytes; its first byte is not 0.
  obtain ⟨first, hfirst, hsel⟩ := Option.bind_eq_some_iff.mp hsel
  have hsel' : 1 ≤ len ∧ first.toNat ≠ 0 := by
    split at hsel
    · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
      omega
    · split at hsel
      · dsimp only at hsel
        split at hsel
        · simp at hsel
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsel
          omega
      · simp at hsel
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hl htake hlt hmax
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hn : (BitVec.ofNat 32 n).toNat = n := by simp; omega
  have hw : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, hn]; simp
  refine ⟨by simp only [CoinbaseScript.zakura, hw]; rw [← not_not.mp htake,
    List.take_append_drop], fun hz => ?_⟩
  have hn0 : n = 0 := by rw [← hn, hz]; rfl
  subst hn0
  rw [show (PushNum.pushNum (BitVec.ofNat 64 0)).toBytes = [0] from pushNum_zero] at htake
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil
    (show scriptSig ≠ [] from fun h => by simp [h] at hfirst)
  simp only [List.head?_cons, Option.some.injEq] at hfirst
  subst hfirst
  have : (b :: rest).take len = b :: rest.take (len - 1) := by
    cases len with
    | zero => omega
    | succ k => simp
  rw [not_not, this, List.cons.injEq] at htake
  exact hsel'.2 (by rw [htake.1]; rfl)

/-- What `Input::zcash_deserialize` returns: an input that spends a coin has a nonzero outpoint
    hash and a script that fits in a protocol message; a coinbase input comes from a `scriptSig`
    of at most `MAX_COINBASE_SCRIPT_LEN` bytes, the genesis one or one `parse_coinbase_height`
    reads. -/
theorem readInput_spec {s s' : List Byte} {input : Input} (h : readInput s = some (input, s')) :
    (∀ o u q, input = .prevOut o u q →
      o.hash.toList ≠ List.replicate 32 0 ∧ u.length ≤ MAX_PROTOCOL_MESSAGE_LEN) ∧
    (∀ height data q, input = .coinbase height data q →
      ∃ scriptSig : List Byte, scriptSig.length ≤ MAX_COINBASE_SCRIPT_LEN ∧
        (scriptSig = GENESIS_COINBASE_SCRIPT_SIG ∧ height = 0 ∧
            data = GENESIS_COINBASE_SCRIPT_SIG ∨
          parseCoinbaseHeight scriptSig = some (height, data))) := by
  obtain ⟨hash, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  split at h
  · obtain ⟨x, s₂, -, h⟩ := Parser.bind_eq_some.mp h
    dsimp only at h
    split at h
    · simp at h
    obtain ⟨len, s₃, -, h⟩ := Parser.bind_eq_some.mp h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i h2 h3
    obtain ⟨scriptSig, s₄, hs, h⟩ := Parser.bind_eq_some.mp h
    have hlen : scriptSig.length ≤ MAX_COINBASE_SCRIPT_LEN := by
      rw [readBytes_length hs]; omega
    split at h
    · rename_i hg
      obtain ⟨⟨height, data⟩, s₅, hp, h⟩ := Parser.bind_eq_some.mp h
      obtain ⟨q, s₆, -, h⟩ := Parser.bind_eq_some.mp h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hp h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hp
      obtain ⟨rfl, -⟩ := h
      refine ⟨fun _ _ _ h => (by cases h), fun height' data' q' h' => ?_⟩
      cases h'
      exact ⟨scriptSig, hlen, Or.inl ⟨hg, rfl, rfl⟩⟩
    · obtain ⟨⟨height, data⟩, s₅, hp, h⟩ := Parser.bind_eq_some.mp h
      obtain ⟨q, s₆, -, h⟩ := Parser.bind_eq_some.mp h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [liftM_apply, Option.map_eq_some_iff, Prod.mk.injEq] at hp
      obtain ⟨⟨height'', data''⟩, hp, hpq, -⟩ := hp
      cases hpq
      refine ⟨fun _ _ _ h => (by cases h), fun height' data' q' h' => ?_⟩
      cases h'
      exact ⟨scriptSig, hlen, Or.inr hp⟩
  · rename_i hz
    obtain ⟨i, s₂, -, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨u, s₃, hu, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨q, s₄, -, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun o u' q' h' => ?_, fun _ _ _ h => by cases h⟩
    cases h'
    exact ⟨hz, readByteVec_le hu⟩

/-- An input Zakura parses as spending a coin has no null outpoint. -/
theorem readInput_notNull {s s' : List Byte} {input : Input}
    (h : readInput s = some (input, s')) (o : OutPoint) (u : List Byte)
    (q : BitVec 32) (he : input = .prevOut o u q) :
    ¬(Input.prevOut o u q).prevoutSpec.IsNull := fun hn =>
  ((readInput_spec h).1 o u q he).1 (by simpa [Input.prevoutSpec, Spec.OutPoint.IsNull] using hn.1)

/-- An input Zakura parses meets the auth digest's hypothesis (`Input.AuthFits`) for its own
    `coinbase_script`. -/
theorem readInput_authFits {s s' : List Byte} {input : Input}
    (h : readInput s = some (input, s')) : input.AuthFits .zakura := by
  obtain ⟨hp, hc⟩ := readInput_spec h
  cases input with
  | prevOut o u q =>
    exact ⟨fun _ _ _ h => (by cases h), by simpa [Input.scriptSig] using (hp o u q rfl).2⟩
  | coinbase height data q =>
    obtain ⟨sig, hlen, hcase⟩ := hc height data q rfl
    have hcs : (Input.coinbase height data q).coinbaseScript .zakura = some sig := by
      rcases hcase with ⟨rfl, rfl, rfl⟩ | hp'
      · simp [Input.coinbaseScript, CoinbaseScript.zakura]
      · obtain ⟨hrt, hne⟩ := parseCoinbaseHeight_spec hp'
        simp only [Input.coinbaseScript, hne, ↓reduceIte, hrt]
    refine ⟨fun _ _ _ _ => by simp [hcs], ?_⟩
    simp only [Input.scriptSig, hcs, Option.getD_some]
    unfold MAX_COINBASE_SCRIPT_LEN at hlen
    unfold MAX_PROTOCOL_MESSAGE_LEN
    omega

/-- What each step of `read_external_count`'s loop guarantees, the whole list does. -/
theorem readCount_forall {α : Type} {read : Parser α} {P : α → Prop}
    (hr : ∀ s s' a, read s = some (a, s') → P a) :
    ∀ n s s' as, readCount read n s = some (as, s') → ∀ a ∈ as, P a := by
  intro n
  induction n with
  | zero =>
    intro s s' as h
    change (pure [] : Parser (List α)) s = some (as, s') at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | succ n ih =>
    intro s s' as h
    obtain ⟨a, s₁, ha, h⟩ := Parser.bind_eq_some.mp h
    obtain ⟨as', s₂, has, h⟩ := Parser.bind_eq_some.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hr _ _ _ ha
    · exact ih _ _ _ has b hb

/-- What each element's parser guarantees, a `Vec` of them does. -/
theorem readVec_forall {α : Type} {read : Parser α} {P : α → Prop}
    (hr : ∀ s s' a, read s = some (a, s') → P a) {s s' : List Byte} {as : List α}
    (h : readVec read s = some (as, s')) : ∀ a ∈ as, P a := by
  obtain ⟨n, s₁, -, h⟩ := Parser.bind_eq_some.mp h
  exact readCount_forall hr n s₁ s' as h

/-- **Zakura's parser gives the native digest theorems their hypotheses** (G3): the transparent
    inputs and outputs it parses (`Vec<Input>`, `Vec<Output>`) have no input spending a coin
    with the null outpoint (`NoNullPrevOut`), each input's `scriptSig` rebuilt and fitting in a
    protocol message (`Input.AuthFits`), and each output's script fitting in one (`CacheFits`,
    which also asks it of the coins spent: outputs Zakura parsed earlier). -/
theorem parse_meets_hypotheses {s₁ s₂ s₃ : List Byte} {inputs : List Input}
    {outputs : List Output} (hi : readVec readInput s₁ = some (inputs, s₂))
    (ho : readVec readOutput s₂ = some (outputs, s₃)) :
    NoNullPrevOut inputs ∧ (∀ i ∈ inputs, i.AuthFits .zakura) ∧
      ∀ o ∈ outputs, o.lockScript.length ≤ MAX_PROTOCOL_MESSAGE_LEN :=
  ⟨fun o u q hm => readVec_forall (P := fun i => ∀ o u q, i = .prevOut o u q →
      ¬(Input.prevOut o u q).prevoutSpec.IsNull) (fun _ _ _ h => readInput_notNull h) hi _ hm
      o u q rfl,
    readVec_forall (fun _ _ _ h => readInput_authFits h) hi,
    readVec_forall (fun _ _ _ h => readOutput_le h) ho⟩

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Native.parse_meets_hypotheses' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms parse_meets_hypotheses

end ZcashSighash.Verifier.Native
