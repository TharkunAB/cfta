# Actual node row bounds

`MergedNodeRowBounds` proves that actual node normalization cannot increase
any selected row count. Canonical identity uniqueness implies that the
complete retained edge list has no duplicates. Its filtered membership
is a subset of the original filtered list. These two facts give the count
bound without a cache or key-coherence premise for the list operation.

`makeNode_filter_length` uses the existing exact complete readback theorem
`EqualityLeafProjectionPhysical.makeNode_edges`. It requires `Coherent`,
`Linked`, and residency of the supplied edges. `makeNode_key_bound` applies
the result to the source symbol/arity `groupKey`. `makeNode_length` gives
the total row count bound. These theorems count rows. They do not measure
constructor, comparison, or solver work.

The pinned Lean 4.34.1 build passed. An isolated audit checked 14,596
imported theorem dependencies and permitted only `propext`,
`Classical.choice`, and `Quot.sound`.
