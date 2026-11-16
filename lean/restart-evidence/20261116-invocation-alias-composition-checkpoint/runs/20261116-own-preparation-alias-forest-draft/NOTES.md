# Own preparation forest

Status: UNCOMPILED. Root owns compilation and publication.

The candidate adds three theorems in `SourcePruningEnumerationOwnAliasForest`.
`suspendMany_forest` uses the actual successful suspension equation. It supports
arbitrary enumeration and native guard types. The proof follows the trie list.
Each literal `CachedChild.allocate heap none` retains the representative forest.
The actual tail equation supplies the next cache.

`prepare_forest` consumes a literal preparation singleton with any returned row
symbol, staged list, and residual. It inverts the actual arity, projection, and
suspension branches. It derives the middle forest from `suspendMany_forest`.
It adds no premise about arity, projection, roots, realization, storage, bounds,
or resources.

`finish_forest` is the unconditional representative projection of the SHARED
`SelectedEdge.finish`. That operation records only the residual obligation.
The existing `finish_protected` at SharedSelectedContinuations line 447 requires
an existing root. It does not export this unconditional forest equality.

All three complete headers and probes were frozen before the proof.
The source uses `autoImplicit false` and default proof limits. Each public
theorem has an appendable `#print axioms` probe. No compiler, Source edit, Git
command, board action, or temporary file was used. This local result does not
prove whole eager alias transport or a simultaneous historical assignment.
