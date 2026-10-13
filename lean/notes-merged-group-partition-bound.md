# Complete-root row bound from source grouping

`MergedGroupPartitionBound.filter_bound` proves a per-key bound on the
flattened output groups. The inputs use actual `Sized.groups key inputs`.
An `All₂` relation gives each returned group a length bound and requires
every returned item to keep the key of every original item in its group.
The theorem derives the complete-root bound from those local facts.

The proof uses induction on the executable partition. The first group
contains its complete key class. The recursive input excludes that key.
`source_output_origin` derives each returned key from an original item.
Thus the first output group and the later output groups cannot both
contribute to the queried key. No global unique-key premise is assumed.
`same_key_group` also proves that two actual groups sharing a key are equal.

`filter_bound_permutation` allows any permutation of the actual source
buckets. `permute_related` constructs the matching output permutation.
Flattening and filtering preserve its row counts. This includes arbitrary
hash-map bucket order while retaining each bucket's source content.

`four_rows` specializes the bound to four. `filter_bound_beq` gives the
same result for lawful Boolean key equality. The pinned Lean 4.34.1 build
passed. The isolated audit checked 14,598 imported theorem dependencies
and permitted only `propext`, `Classical.choice`, and `Quot.sound`.
