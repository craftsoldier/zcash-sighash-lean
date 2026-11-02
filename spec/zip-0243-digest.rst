.. Source: zcash/zips commit ff594de6e95bb9e9e7d2ace09510281531c30447, zips/zip-0243.rst lines 40-135
.. ZIP 243 "Transaction Signature Validation for Sapling", sections Specification and Field definitions
.. Pinned: 2026-11-02

Specification
=============

A new transaction digest algorithm is defined::

  BLAKE2b-256 hash of the serialization of:
    1. header of the transaction (4-byte little endian)
    2. nVersionGroupId of the transaction (4-byte little endian)
    3. hashPrevouts (32-byte hash)
    4. hashSequence (32-byte hash)
    5. hashOutputs (32-byte hash)
    6. hashJoinSplits (32-byte hash)
    7. hashShieldedSpends (32-byte hash)
    8. hashShieldedOutputs (32-byte hash)
    9. nLockTime of the transaction (4-byte little endian)
   10. nExpiryHeight of the transaction (4-byte little endian)
   11. valueBalance of the transaction (8-byte little endian)
   12. sighash type of the signature (4-byte little endian)

   13. If we are computing a transaction digest for a transparent input (i.e. this hash is not for
       a JoinSplit signature, Spend authorization signature, or binding signature):
       a. outpoint (32-byte hash + 4-byte little endian) 
       b. scriptCode of the input (serialized as scripts inside CTxOuts)
       c. value of the output spent by this input (8-byte little endian)
       d. nSequence of the input (4-byte little endian)

The new algorithm is based on the transaction digest algorithm defined in ZIP 143 [#zip-0143]_.

The new algorithm MUST be used for signatures created over the Sapling transaction format [#protocol]_.
Combined with the new consensus rule that v3 transaction formats will be invalid from the Sapling upgrade,
this effectively means that all transaction signatures from the Sapling activation height (as specified
in [#zip-0205]_) will use the new algorithm.

The BLAKE2b-256 personalization field [#BLAKE2-personalization]_ is set to::

  "ZcashSigHash" || CONSENSUS_BRANCH_ID

``CONSENSUS_BRANCH_ID`` is the 4-byte little-endian encoding of the consensus branch ID for the epoch of
the block containing the transaction. [#zip-0200]_ Domain separation of the signature hash across parallel
consensus branches provides replay protection: transactions targeted for one consensus branch will have
invalid signatures on other consensus branches.

Transaction creators MUST specify the epoch they want their transaction to be mined in. Across a network
upgrade, this means that if a transaction is not mined before the activation height, it will never be mined.

Semantics of the original sighash types are as in ZIP 143 [#zip-0143]_.

Field definitions
-----------------

The items 1, 2, 3, 4, 5, 9, 10, 12, and 13 have the same meaning as in ZIP 143 [#zip-0143]_.

6: ``hashJoinSplits``
`````````````````````
* If ``vjoinsplits`` is non-empty, ``hashJoinSplits`` is the BLAKE2b-256 hash of the serialization of all
  JoinSplit descriptions (in their canonical v4 transaction serialization format) concatenated with the
  ``joinSplitPubKey``;

  * The BLAKE2b-256 personalization field is set to ``ZcashJSplitsHash``.

  * Note that while signatures are omitted, the JoinSplit proofs are included in the signature hash, as with
    v1, v2, and v3 transactions.

* Otherwise, ``hashJoinSplits`` is a ``uint256`` of ``0x0000......0000``.

7: ``hashShieldedSpends``
`````````````````````````

* If ``vShieldedSpend`` is non-empty, ``hashShieldedSpends`` is the BLAKE2b-256 hash of the serialization of
  all Spend Descriptions (in their canonical transaction serialization format minus ``spendAuthSig``);

  * The BLAKE2b-256 personalization field is set to ``ZcashSSpendsHash``.

  * Note that the Spend proofs are included in the signature hash, as with JoinSplit proofs in v1, v2, and v3
    transactions.

* Otherwise, ``hashShieldedSpends`` is a ``uint256`` of ``0x0000......0000``.

8: ``hashShieldedOutputs``
``````````````````````````

* If ``vShieldedOutput`` is non-empty, ``hashShieldedOutputs`` is the BLAKE2b-256 hash of the serialization of
  all Output Descriptions (in their canonical transaction serialization format);

  * The BLAKE2b-256 personalization field is set to ``ZcashSOutputHash``.

  * Note that the Output proofs are included in the signature hash, as with JoinSplit proofs in v1, v2, and v3
    transactions.

* Otherwise, ``hashShieldedOutputs`` is a ``uint256`` of ``0x0000......0000``.

11: ``valueBalance``
````````````````````
An 8-byte signed two's-complement little-endian value of the net amount, in zatoshi, exiting the Sapling value
pool. For clarity, a negative value corresponds to an amount *entering* the Sapling value pool.

