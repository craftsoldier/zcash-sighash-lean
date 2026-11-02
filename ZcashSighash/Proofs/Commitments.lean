/-
What a transaction's identifier and auth digest commit to. The identifier commits to the
effecting data and ignores the authorizing data (ZIP 244: "TxId Digest"; in version 6 the anchors
are authorizing data, ZIP 229). A cache keyed by identifier alone therefore cannot tell two
transactions with different signatures or proofs apart, as Zebra's CVE-2026-34377 (GHSA-3vmh)
showed; keying it by identifier and auth digest can.
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

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Spec.txid_stripAuth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms txid_stripAuth

end ZcashSighash.Spec
