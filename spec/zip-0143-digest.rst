.. Source: zcash/zips commit ff594de6e95bb9e9e7d2ace09510281531c30447, zips/zip-0143.rst lines 68-196
.. ZIP 143 "Transaction Signature Validation for Overwinter", section Specification
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
    7. nLockTime of the transaction (4-byte little endian)
    8. nExpiryHeight of the transaction (4-byte little endian)
    9. sighash type of the signature (4-byte little endian)
   10. If we are computing a transaction digest for a transparent input (i.e. this is not a JoinSplit
       signature hash):
       a. outpoint (32-byte hash + 4-byte little endian)
       b. scriptCode of the input (serialized as scripts inside CTxOuts)
       c. value of the output spent by this input (8-byte little endian)
       d. nSequence of the input (4-byte little endian)

The new algorithm is based on the Bitcoin transaction digest algorithm defined in BIP 143, [#bip-0143]_ with
replay protection inspired by BUIP-HF v1.2. [#buip-HF]_

The new algorithm MUST be used for signatures created over the Overwinter transaction format. [#zip-0202]_
Combined with the new consensus rule that v1 and v2 transaction formats will be invalid from the Overwinter
upgrade, [#zip-0202]_ this effectively means that all transaction signatures from the Overwinter activation
height will use the new algorithm. [#zip-0201]_

The BLAKE2b-256 personalization field [#BLAKE2-personalization]_ is set to::

  "ZcashSigHash" || CONSENSUS_BRANCH_ID

``CONSENSUS_BRANCH_ID`` is the 4-byte little-endian encoding of the consensus branch ID for the epoch of
the block containing the transaction. [#zip-0200]_ Domain separation of the signature hash across parallel
consensus branches provides replay protection: transactions targeted for one consensus branch will have
invalid signatures on other consensus branches.

Transaction creators MUST specify the epoch they want their transaction to be mined in. Across a network
upgrade, this means that if a transaction is not mined before the activation height, it will never be mined.

Semantics of the original sighash types remain unchanged, except the following:

#. The serialization format is changed;

#. All sighash types commit to the amount being spent by the signed input;

#. ``SINGLE`` does not commit to the input index. When ``ANYONECANPAY`` is not set, the semantics are
   unchanged since ``hashPrevouts`` and ``outpoint`` together implictly commit to the input index. When
   ``SINGLE`` is used with ``ANYONECANPAY``, omission of the index commitment allows permutation of the
   input-output pairs, as long as each pair is located at an equivalent index.

Field definitions
-----------------

The items 7, 9, 10a, 10d have the same meaning as the original algorithm from Bitcoin. [#wiki-checksig]_

1: ``header``
`````````````
Deserialized into two transaction properties: ``fOverwintered`` and ``nVersion``. For transactions that use
this transaction digest algorithm, ``fOverwintered`` is always set. [#zip-0202]_

2: ``nVersionGroupId``
``````````````````````
Provides domain separation of ``nVersion``. It is only defined if ``fOverwintered`` is set, which means that
it is always defined for transactions that use this algorithm. [#zip-0202]_

3: ``hashPrevouts``
```````````````````
* If the ``ANYONECANPAY`` flag is not set, ``hashPrevouts`` is the BLAKE2b-256 hash of the serialization of
  all input outpoints;

  * The BLAKE2b-256 personalization field is set to ``ZcashPrevoutHash``.

* Otherwise, ``hashPrevouts`` is a ``uint256`` of ``0x0000......0000``.

4: ``hashSequence``
```````````````````
* If none of the ``ANYONECANPAY``, ``SINGLE``, ``NONE`` sighash type is set, ``hashSequence`` is the
  BLAKE2b-256 hash of the serialization of ``nSequence`` of all inputs;

  * The BLAKE2b-256 personalization field is set to ``ZcashSequencHash``.

* Otherwise, ``hashSequence`` is a ``uint256`` of ``0x0000......0000``.

Note: the encoding of the sighash type is masked with ``0x1F`` when checking whether or not the ``SINGLE``
and ``NONE`` flags are set.

5: ``hashOutputs``
``````````````````
* If the sighash type is neither ``SINGLE`` nor ``NONE``, ``hashOutputs`` is the BLAKE2b-256 hash of the
  serialization of all output amount (8-byte little endian) with ``scriptPubKey`` (serialized as scripts
  inside CTxOuts);

* If sighash type is ``SINGLE`` and the input index is smaller than the number of outputs, ``hashOutputs`` is
  the BLAKE2b-256 hash of the output (serialized as above) with the same index as the input;

  * The BLAKE2b-256 personalization field is set to ``ZcashOutputsHash`` in both cases above.

* Otherwise, ``hashOutputs`` is a ``uint256`` of ``0x0000......0000``. [#01-change]_

Note: the encoding of the sighash type is masked with ``0x1F`` when checking whether or not the ``SINGLE``
and ``NONE`` flags are set.

6: ``hashJoinSplits``
`````````````````````
* If ``vjoinsplits`` is non-empty, ``hashJoinSplits`` is the BLAKE2b-256 hash of the serialization of all
  JoinSplits (in their canonical transaction serialization format) concatenated with the joinSplitPubKey;

  * The BLAKE2b-256 personalization field is set to ``ZcashJSplitsHash``.

  * Note that while signatures are omitted, the JoinSplit proofs are included in the signature hash, as with
    v1 and v2 transactions.

* Otherwise, ``hashJoinSplits`` is a ``uint256`` of ``0x0000......0000``.

8: ``nExpiryHeight``
````````````````````
The block height after which the transaction becomes unilaterally invalid, and can never be mined. [#zip-0203]_

10b: ``scriptCode``
```````````````````
The script being currently executed: ``redeemScript`` for P2SH, or ``scriptPubKey`` in the general case. This
is the same script as serialized in the Sprout transaction digest algorithm.

10c: value
``````````
An 8-byte little-endian value of the amount, in zatoshi, spent in this input.
