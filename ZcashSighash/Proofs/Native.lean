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

-- The build fails if a theorem rests on anything beyond Lean's three axioms.
/--
info: 'ZcashSighash.Verifier.Native.EMPTY_IRONWOOD_AUTH_HASH_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms EMPTY_IRONWOOD_AUTH_HASH_eq

end ZcashSighash.Verifier.Native
