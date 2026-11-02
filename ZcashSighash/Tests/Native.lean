/-
Zakura's own ZIP 244 / ZIP 229 digests on ZIP 244's test vectors and the two version 6
transactions: each transaction's identifier and auth digest, its shielded signature digest, and
its transparent input's signature digest under each hash type the vector gives one for.
-/
import ZcashSighash.Verifier.Native
import ZcashSighash.Tests.Spec

namespace ZcashSighash.Tests

open ZcashSighash.Spec
open ZcashSighash.Verifier
open ZcashSighash.Verifier.Native (Parts CoinbaseScript Zip244SighashCache)

/-- A coinbase input's `scriptSig`, if the transaction has one: a test vector's coinbase
    `scriptSig` need not encode a height, so the test rebuilds it whole. -/
def coinbaseScriptSig (tx : Spec.Transaction) : List Byte :=
  match (tx.transparent.vin.zip tx.scriptSigs).find? (·.1.prevout.IsNull) with
  | some (_, s) => s
  | none => []

/-- `push_num` that rebuilds the transaction's coinbase `scriptSig`, with empty data. -/
def coinbaseScriptOf (tx : Spec.Transaction) : CoinbaseScript :=
  ⟨fun _ => coinbaseScriptSig tx, []⟩

/-- A decoded transaction as Zakura's parser holds it: a null prevout as a coinbase input, each
    component only when it is not empty. -/
def toParts (tx : Spec.Transaction) : Parts where
  version := match tx.format with | .v5 => .v5 | .v6 _ => .v6
  consensusBranchId := tx.header.consensusBranchId
  lockTime := tx.header.lockTime
  expiryHeight := tx.header.expiryHeight
  inputs := (tx.transparent.vin.zip tx.scriptSigs).map fun (i, s) =>
    if i.prevout.IsNull then .coinbase 1 [] i.nSequence
    else .prevOut ⟨i.prevout.hash, i.prevout.n⟩ s i.nSequence
  outputs := tx.transparent.vout.map fun o => ⟨o.value, o.scriptPubKey⟩
  sapling :=
    let spends := tx.sapling.spends.map fun s => (⟨s.cv, s.nullifier, s.rk, s.zkproof,
      s.spendAuthSig⟩ : Native.SaplingSpend)
    let outputs := tx.sapling.outputs.map fun o => (⟨o.cv, o.cmu, o.ephemeralKey, o.encCiphertext,
      o.outCiphertext, o.zkproof⟩ : Native.SaplingOutput)
    match spends, outputs with
    | [], [] => none
    | sp :: sps, os => some ⟨tx.sapling.valueBalance,
        .spendsAndMaybeOutputs tx.sapling.anchor ⟨sp, sps⟩ os, tx.sapling.bindingSig⟩
    | [], o :: os => some ⟨tx.sapling.valueBalance, .justOutputs ⟨o, os⟩, tx.sapling.bindingSig⟩
  orchard := orchardData tx.orchard
  ironwood := match tx.format with | .v5 => none | .v6 iw => orchardData iw
where
  /-- An Orchard-shaped component, only when it has an Action. -/
  orchardData (b : OrchardBundle) : Option Native.OrchardData :=
    match b.actions.map fun a => (⟨a.cv, a.nullifier, a.rk, a.cmx, a.ephemeralKey,
        a.encCiphertext, a.outCiphertext, a.spendAuthSig⟩ : Native.Action) with
    | [] => none
    | a :: as => some ⟨b.flags, b.valueBalance, b.anchor, b.proofs, ⟨a, as⟩, b.bindingSig⟩

/-- The coins the inputs spend, as Zakura's previous outputs. -/
def previousOutputs (tx : Spec.Transaction) : List Native.Output :=
  tx.transparent.vin.map fun i => ⟨i.spent.value, i.spent.scriptPubKey⟩

/-- The canonical hash type of a specification hash type. -/
def canonical (h : HashType) : Native.CanonicalHashType :=
  match h.base, h.anyoneCanPay with
  | .all, false => .all
  | .none, false => .none
  | .single, false => .single
  | .all, true => .allAnyoneCanPay
  | .none, true => .noneAnyoneCanPay
  | .single, true => .singleAnyoneCanPay

/-- Whether Zakura's native code gives the vector's digests. -/
def checkNative (v : Zip244Vector) : Bool :=
  match decode (hex v.tx) (v.amounts.zip v.scriptPubKeys |>.map
      fun (a, s) => ⟨.ofNat _ a, hex s⟩) with
  | none => false
  | some tx =>
    let p := toParts tx
    match Zip244SighashCache.new p (previousOutputs tx) with
    | none => false
    | some cache =>
      Native.txid p == some (hex v.txid) &&
      Native.authDigest (coinbaseScriptOf tx) p == some (hex v.authDigest) &&
      cache.sighash .all none == some (hex v.sighashShielded) &&
      match v.transparentInput with
      | none => true
      | some i => (hashTypes v).all fun (ht, expected) =>
        match expected with
        | some e => cache.sighash (canonical ht) (some i) == some (hex e)
        -- No digest: `SIGHASH_SINGLE` without a corresponding output, which the callback
        -- refuses before calling the cache (`Proofs/Script.lean`).
        | none => !cache.hasCorrespondingOutput i

#guard zip244Vectors.map checkNative = List.replicate 10 true

/-- Whether Zakura's native code gives the version 6 vector's digests. -/
def checkNativeV6 (v : V6Vector) : Bool :=
  let p := toParts v.tx
  match Zip244SighashCache.new p (previousOutputs v.tx), hashHeaderOf p with
  | some cache, some header =>
    header == hex v.headerDigest &&
    Native.txid p == some (hex v.txid) &&
    (v.authDigest.all fun d => Native.authDigest (coinbaseScriptOf v.tx) p == some (hex d)) &&
    v.sighashShielded.all fun d => cache.sighash .all none == some (hex d)
  | _, _ => false
where
  /-- The header digest. -/
  hashHeaderOf (p : Parts) : Option Blake2bHash := Native.hashHeader p

#guard v6Vectors.map checkNativeV6 = [true, true]

/-! ## A coinbase input's `scriptSig` -/

/-- A `push_num` that writes the height's low byte after a one-byte push, and a genesis script:
    enough to tell the cases of `Input::coinbase_script` apart. -/
def testCoinbaseScript : CoinbaseScript :=
  ⟨fun h => [0x01, h.setWidth 8], [0x04, 0xff, 0xff, 0x00, 0x1d]⟩

-- A coinbase input above genesis: `push_num(height)` then its data.
#guard (Native.Input.coinbase 0x2a [0xaa, 0xbb] 0).coinbaseScript testCoinbaseScript ==
  some [0x01, 0x2a, 0xaa, 0xbb]

-- The genesis coinbase input: its data is the whole genesis script.
#guard (Native.Input.coinbase 0 [0x04, 0xff, 0xff, 0x00, 0x1d] 0).coinbaseScript
    testCoinbaseScript == some [0x04, 0xff, 0xff, 0x00, 0x1d]

-- A height 0 input with other data has no `scriptSig` (`coinbase_script`'s `expect` panics).
#guard (Native.Input.coinbase 0 [0xaa] 0).coinbaseScript testCoinbaseScript == none

-- A non-coinbase input has none to rebuild.
#guard (Native.Input.prevOut ⟨List.Vector.replicate 32 1, 0⟩ [0xaa] 0).coinbaseScript
    testCoinbaseScript == none

end ZcashSighash.Tests
