# Constructed sparse-to-complete identity map

`SourceIdentityMap.names` pairs the executed sparse and complete logical names
at every actual position. `functional` proves that duplicate source keys have
one target. `keys_unique` proves that pair deduplication makes the source keys
unique. `rename_actual` and `environment_actual` execute that map and its
environment pullback at every source actual position.

`complete_count_le_one` proves that a source value without a sparse conflict
cannot gain a conflict when complete subtree equality merges classes.
`unallocated_complete` proves the corresponding source allocation lookup is
absent. `used_fixed` then proves that the identity map fixes every name in the
original source avoid list, including free formula names and formal names.

These facts do not imply complete nested-query transport. The map can
identify a generated sparse name with a formal's ambient name. It is then
not injective on the names which later scopes read. `NestedScopeCapture`
proves that this is an actual semantic obstruction, not a missing proof
technique: an outer scope can change the complete ambient actual name while
leaving the sparse fresh name unchanged. The pruning repair therefore
retains the original guard whenever the source identity test is ambiguous.

Validation: `lake build MicroCFTA.SourceIdentityMap` succeeds with the pinned
Lean toolchain. No source correctness claim depends on an assumed injective
identity merge.
