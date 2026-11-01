<!-- Source: zcash/zips commit ff594de6e95bb9e9e7d2ace09510281531c30447, zips/zip-0229.md lines 353-498 -->
<!-- ZIP 229 "Version 6 Transaction Format", sections Transaction Identifiers to Block Commitments -->
<!-- Pinned: 2026-11-01 -->

## Transaction Identifiers, Auth Digests, and Signature Digests

Version 6 transaction identifiers (txids), authorizing-data commitments ("auth digests"),
and signature digests are computed as in ZIP 244 [^zip-0244], with two changes: an
**Ironwood component digest** is added, and for version 6 the Sapling, Orchard and Ironwood
anchors move from effecting data to authorizing data. The version 5 algorithm is unchanged.

### Ironwood component digest

Relative to the txid digest for v5 transactions [^zip-0244-txiddigest], the version 6
txid digest adds an Ironwood component digest as the last child, after the Orchard component
digest:

    txid_digest_v6 = BLAKE2b-256("ZcashTxHash_" || consensusBranchId,
                                 header_digest || transparent_digest || sapling_digest_v6 ||
                                 orchard_digest_v6 || ironwood_digest_v6)

Relative to the auth digest for v5 transactions [^zip-0244-authorizingdatacommitment], the
version 6 auth digest adds an Ironwood auth digest as the last child, after the Orchard one:

    auth_digest_v6 = BLAKE2b-256("ZTxAuthHash_" || consensusBranchId,
                                 transparent_auth_digest || sapling_auth_digest_v6 ||
                                 orchard_auth_digest_v6 || ironwood_auth_digest_v6)

### Anchor commitment (version 6)

In version 5, the Sapling anchor (encoded redundantly as `anchor` in each
`sapling_spends_noncompact_digest`) and the Orchard anchor (`anchorOrchard` in `orchard_digest`)
are part of the **effecting data**: they are committed to in `txid_digest`, while the Sapling and
Orchard auth digests commit only to proofs and signatures [^zip-0244-authorizingdatacommitment].

In version 6, for Sapling, Orchard, and Ironwood components, the anchor is instead part of the
**authorizing data**. Relative to ZIP 244, for version 6 transactions:

- `sapling_spends_noncompact_digest_v6`, `orchard_digest_v6`, and `ironwood_digest_v6` omit the anchor.
- `sapling_auth_digest_v6`, `orchard_auth_digest_v6`, and `ironwood_auth_digest_v6` additionally commit
  to `anchorSapling`, `anchorOrchard`, or `anchorIronwood` respectively, after the existing fields.
  As in the serialization, each anchor is present only when its component has a spend or
  action referencing it: `anchorSapling` iff `nSpendsSapling > 0`, `anchorOrchard` iff
  `nActionsOrchard > 0`, and `anchorIronwood` iff `nActionsIronwood > 0`. In particular,
  a Sapling component with outputs but no spends (for example a transparent-to-Sapling
  transfer) commits to no `anchorSapling`.

This lets the anchor be updated (re-anchored to a more recent note commitment tree root) without
changing the transaction ID, while the proofs still bind to the specific anchor used.

`ironwood_digest_v6` and `ironwood_auth_digest_v6` are computed with *the same structure* as
`orchard_digest_v6` and `orchard_auth_digest_v6`, but with Ironwood-specific 16-byte BLAKE2b-256
personalizations at each node. Also, distinct personalizations are used for Sapling and Orchard nodes
where what is directly hashed has been affected as a result of moving the anchor commitments to auth
data, as follows:

| Node                                    | v5 personalization | v6 personalization | Comment for v6            |
|:--------------------------------------- | ------------------ | ------------------ | ------------------------- |
| $\hspace{22em}$ **Sapling** ||||
| `sapling_digest[_v6]`                   | `ZTxIdSaplingHash` | `ZTxIdSaplingHash` | not changed directly      |
| `sapling_spends_digest`                 | `ZTxIdSSpendsHash` | `ZTxIdSSpendsHash` | unchanged                 |
| `sapling_spends_compact_digest`         | `ZTxIdSSpendCHash` | `ZTxIdSSpendCHash` | unchanged                 |
| `sapling_spends_noncompact_digest[_v6]` | `ZTxIdSSpendNHash` | `ZTxIdSSpendNH_v6` | omits `anchor`            |
| `sapling_auth_digest[_v6]`              | `ZTxAuthSapliHash` | `ZTxAuthSapliH_v6` | includes `anchorSapling`  |
| $\hspace{22em}$ **Orchard** ||||
| `orchard_digest[_v6]`                   | `ZTxIdOrchardHash` | `ZTxIdOrchardH_v6` | omits `anchorOrchard`     |
| `orchard_actions_compact_digest`        | `ZTxIdOrcActCHash` | `ZTxIdOrcActCHash` | unchanged                 |
| `orchard_actions_memos_digest`          | `ZTxIdOrcActMHash` | `ZTxIdOrcActMHash` | unchanged                 |
| `orchard_actions_noncompact_digest`     | `ZTxIdOrcActNHash` | `ZTxIdOrcActNHash` | unchanged                 |
| `orchard_auth_digest[_v6]`              | `ZTxAuthOrchaHash` | `ZTxAuthOrchaH_v6` | includes `anchorOrchard`  |
| $\hspace{22em}$ **Ironwood** ||||
| `ironwood_digest_v6`                    | n/a                | `ZTxIdIronwd_H_v6` | omits `anchorIronwood`    |
| `ironwood_actions_compact_digest_v6`    | n/a                | `ZTxIdIrnActCH_v6` |                           |
| `ironwood_actions_memos_digest_v6`      | n/a                | `ZTxIdIrnActMH_v6` |                           |
| `ironwood_actions_noncompact_digest_v6` | n/a                | `ZTxIdIrnActNH_v6` |                           |
| `ironwood_auth_digest_v6`               | n/a                | `ZTxAuthIrnwdH_v6` | includes `anchorIronwood` |

As in the case of Sapling and Orchard, when a version 6 transaction has no Ironwood actions,
`ironwood_digest_v6` and `ironwood_auth_digest_v6` are the hashes of empty input under the component
and auth personalizations respectively, i.e. `BLAKE2b-256("ZTxIdIronwd_H_v6", [])` and
`BLAKE2b-256("ZTxAuthIrnwdH_v6", [])`, which are distinct from the Orchard empty-component digests.

### Summary of the resulting digest structure

Below, `(*)` indicates a node that is directly changed relative to v5, and `(+)` indicates a node
that is added relative to v5.

The txid digest structure becomes:

    txid_digest_v6
    ├── header_digest
    ├── transparent_digest
    │   ├── prevouts_digest
    │   ├── sequence_digest
    │   └── outputs_digest
    ├── sapling_digest_v6
    │   ├── sapling_spends_digest_v6
    │   │   ├── sapling_spends_compact_digest
    │   │   └── sapling_spends_noncompact_digest_v6 (*)
    │   │       ├── cv
    │   │       └── rk
    │   ├── sapling_outputs_digest
    │   │   ├── sapling_outputs_compact_digest
    │   │   ├── sapling_outputs_memos_digest
    │   │   └── sapling_outputs_noncompact_digest
    │   └── valueBalance
    ├── orchard_digest_v6 (*)
    │   ├── orchard_actions_compact_digest
    │   ├── orchard_actions_memos_digest
    │   ├── orchard_actions_noncompact_digest
    │   ├── flagsOrchard
    │   └── valueBalanceOrchard
    └── ironwood_digest_v6 (+)
        ├── ironwood_actions_compact_digest_v6
        ├── ironwood_actions_memos_digest_v6
        ├── ironwood_actions_noncompact_digest_v6
        ├── flagsIronwood
        └── valueBalanceIronwood

The auth digest structure becomes:

    auth_digest_v6
    ├── transparent_scripts_digest
    ├── sapling_auth_digest_v6 (*)
    │   ├── vSpendProofsSapling
    │   ├── vSpendAuthSigsSapling
    │   ├── vOutputProofsSapling
    │   ├── bindingSigSapling
    │   └── anchorSapling (+)
    ├── orchard_auth_digest_v6 (*)
    │   ├── proofsOrchard
    │   ├── vSpendAuthSigsOrchard
    │   ├── bindingSigOrchard
    │   └── anchorOrchard (+)
    └── ironwood_auth_digest_v6 (+)
        ├── proofsIronwood
        ├── vSpendAuthSigsIronwood
        ├── bindingSigIronwood
        └── anchorIronwood

Note that the nodes under each of `sapling_digest_v6`, `orchard_digest_v6`, `ironwood_digest_v6`,
and their `auth_digest`s are present only if the corresponding component is non-empty.

## Block Commitments

The `hashAuthDataRoot` component of `hashBlockCommitments` [^zip-0244] incorporates the version 6 auth
digest — which now includes the Ironwood auth digest, and (per the change above) the anchors — with
no further structural change.


