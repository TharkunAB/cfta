# Actual logical names and complete identity classes

`SourceLogicalNames.lean` connects both source table lookups. The source
allocates by representative path, then copies an optional declaration to
each actual path. `copied_lookup` proves that the second lookup retains the
first lookup's result exactly. It uses the actual observation records to
prove that one path cannot contain two different actual records.

`allocated_sources` and `allocated_fresh` recover both complete projections
of the source allocation zip. `allocated_name_unique` proves that no two
allocated rows share a generated name. `unallocated_same_class` covers the
other allocation arm: if an actual needs no declaration, every actual with
that original name has the same representative. Its proof uses the source
count predicate and duplicate-free representative/name values.

`logicalName_class` combines these cases. Equal logical names imply equal
representative classes. Allocated names cannot collide with original names
because the actual source avoid list contains every original actual name.
`sparse_name_same_term` connects this result to complete subtree equality.
`sparse_name_complete_name` then proves that the complete logical-name
function is constant on each sparse logical-name class.

These results establish that the source sparse-to-complete logical-name map
is a function. They do not yet construct the full query substitution map or
prove all query environment and sort-domain transport for identity merges.

Validation: `lake build MicroCFTA.SourceLogicalNames` succeeds with the pinned
Lean toolchain. No production source changed.
