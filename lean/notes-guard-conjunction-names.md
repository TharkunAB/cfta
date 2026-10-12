# Global name allocation survives conjunction normalization

`GuardConjunctionNames.lean` completes the public evaluator proof for the
outer conjunction normalization in `GuardConjunction`. It proves membership
preservation for paths, actual paths, symbol-sensitive paths, and literal
requirements. `orderedPaths_ext` connects the source comparison-based path
sort to the proved canonical path representation. Ordered path sets and the
complete actual observation table are therefore exactly unchanged.

`freshNames_ext` proves that the executed finite allocator depends only on
avoid-list membership. The source candidate prefix uses the avoid-list
length. The proof handles this length change explicitly: the shorter prefix
already contains enough retained names by `SourceActuals.fresh_length`, so
extending the prefix cannot change the first requested names.

`allocated_normalize` and `substitutionValues_normalize` prove exact equality
of allocation rows, copied per-path declarations, and ambiguity lists. These
are list equalities, not only set or mathematical formula equivalences.
Duplicate removal and requirement reordering cannot change fresh spellings.

`evaluateGuardWithSame_normalize` combines those tables with the complete
fixed-table guard traversal theorem. Both public wrappers follow:
`evaluateGuard_normalize` and `evaluateGuardWithShape_normalize`. They retain
Yes, No, and Unknown for any stable pure solver callback. They need no solver
renaming contract because the actual names and query formulas stay equal.
An effectful callback still needs the separately stated repeated-query and
query-order contract; this theorem does not compare IO traces.

Validation: `lake build MicroCFTA.GuardConjunctionNames` succeeds with the
pinned toolchain. The proof does not assume a bound on conjunction size or
actual conflicts. No production source changed in this milestone.
