.. Source: zcash/zips commit ff594de6e95bb9e9e7d2ace09510281531c30447, zips/zip-0244.rst lines 743-800
.. ZIP 244 "Transaction Identifier Non-Malleability", section Block Header Changes
.. Pinned: 2026-11-02

--------------------
Block Header Changes
--------------------

The nonmalleable transaction identifier specified by this ZIP will be used
in the place of the current malleable transaction identifier within the
Merkle tree committed to by the ``hashMerkleRoot`` value. However, this
change now means that ``hashMerkleRoot`` is not sufficient to fully commit
to the transaction data, including witnesses, that appear within the block.

As a consequence, we now need to add a new commitment to the block header.
This commitment will be the root of a Merkle tree having leaves that are
transaction authorizing data commitments, produced according to the
`Authorizing Data Commitment`_ part of this specification. The insertion
order for this Merkle tree MUST be identical to the insertion order of
transaction identifiers into the Merkle tree that is used to construct
``hashMerkleRoot``, such that a path through this Merkle tree to a
transaction identifies the same transaction as that path reaches in the tree
rooted at ``hashMerkleRoot``.

This new commitment is named ``hashAuthDataRoot`` and is the root of a
binary Merkle tree of transaction authorizing data commitments having height
$\mathsf{ceil(log_2(tx\_count))}$, padded with leaves having the "null"
hash value ``[0u8; 32]``. Note that $\mathsf{log_2(tx\_count)}$ is
well-defined because $\mathsf{tx\_count} > 0$, due to the coinbase
transaction in each block. Non-leaf hashes in this tree are BLAKE2b-256
hashes personalized by the string ``"ZcashAuthDatHash"``.

Changing the block header format to allow space for an additional
commitment is somewhat invasive. Instead, the name and meaning of the
``hashLightClientRoot`` field, described in ZIP 221 [#zip-0221]_, is changed.

``hashLightClientRoot`` is renamed to ``hashBlockCommitments``. The value
of this hash is the BLAKE2b-256 hash personalized by the string ``"ZcashBlockCommit"``
of the following elements::

   hashLightClientRoot (as described in ZIP 221)
   hashAuthDataRoot    (as described below)
   terminator          [0u8;32]

This representation treats the ``hashBlockCommitments`` value as a linked
list of hashes terminated by arbitrary data. In the case of protocol upgrades
where additional commitments need to be included in the block header, it is
possible to replace this terminator with the hash of a newly defined structure
which ends in a similar terminator. Fully validating nodes MUST always use the
entire structure defined by the latest activated protocol version that they
support.

The linked structure of this hash is intended to provide extensibility for
use by light clients which may be connected to a third-party server that supports
a later protocol version. Such a third party SHOULD provide a value that can
be used instead of the all-zeros terminator to permit the light client to
perform validation of the parts of the structure it needs.

Unlike the ``hashLightClientRoot`` change, the change to ``hashBlockCommitments``
happens in the block that activates this ZIP.

The block header byte format and version are not altered by this ZIP.
