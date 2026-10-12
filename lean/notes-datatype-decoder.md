# Hashed datatype decoding

`DatatypeDecoder` follows `datatypeDecoder` in
`Data.CFTA.Gen.Internal.Automaton`. It builds one table from the flattened
constructor rows. The hash selects a bucket. A full-symbol equality lookup
then selects the constructor. New entries precede old entries within each
bucket, as `IntMap.fromListWith (<>)` specifies.

`insert_find` proves the exact effect of each insertion. `find_exact` derives
equality with a direct full-key map for every hash function. It includes
collisions, repeated labels, unknown labels, and last-entry precedence. It
does not assume that a symbol hash is unique. The kernel examples use a
constant hash for all labels.

`restore` traverses the entire ordered term with the optional constructor
lookup. `restore_iff` compares that operation with an independent pointwise
constructor relation. `restore_table_iff` connects the relation to the actual
stored table when repeated full labels identify the same constructor.
`decode_exact` proves that optimized decoding returns exactly the same result
as direct full-key restoration followed by the typed codec. This theorem
applies to partial and noninjective codecs too.

`constructor_table_coherent` derives table coherence from distinct labels on
the actual constructor set. `decode_labelled` proves that an admitted typed
constructor term reaches its original codec unchanged after relabelling and
hashed restoration. `ranked_total` and `ranked_injective` connect that result
to the existing codec and distinct-rank contracts. Value injectivity still
requires the codec's encode-after-decode law. Constructor probes do not prove
that law or codec totality on arbitrary terms.

`comparisons_bound` bounds full-symbol comparisons by the selected bucket
length. `lookup_cost_bound` bounds them by the total stored constructor count.
An absent symbol in a colliding bucket examines every entry, as
`absent_comparisons` proves. No constant-time hash-table or uniform-hash
assumption is needed for the semantic result. Physical IntMap lookup and
cached Symbol hashing remain runtime operations.

The full-symbol key is an explicit parameter. The source's interned Symbol
equality, `constructorLabel` text encoding, GHC type metadata, and packed-term
traversal retain their representation contracts. The source term traversal is
strictly shape-preserving; it does not interpret automaton constraints.

Validation uses the pinned Lean toolchain. The focused build passes all nine
jobs. No Haskell source changed.
