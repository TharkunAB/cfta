# Inherited equality reduction

`PartialReductionCaller` models the schedule in
`Data.CFTA.Equality.Operations.reducePartially'`. It uses the previously proved
`EqualityReduction.reduce` worker for each edge. The caller then combines the
inherited classes with the original edge classes, descends that result by
child position, recursively reduces the narrowed children, and modifies the
original ordinary node. Every rebuilt edge retains its label and full guard.

The source stops descent at `Mu` and explicit union nodes. The Mu case is
`go _ (Mu n) = Mu n`. It invokes the smart constructor and can apply binder
cleanup. The model therefore calls `rebuildBinder` and requires its local
language law. It does not assume node identity. Explicit unions and empty
nodes return unchanged. An unresolved reference is a source error.

`combine` runs the existing total equality normalizer on inherited and local
classes. `combine_exact` derives its conjunction semantics.
`combine_finishes` excludes normalization timeout at the proved bound.
The contradiction branch maps every narrowed child to the empty node. It
cannot retain a guarded term that satisfies the inherited constraints.

`walk_forest` derives the meaning of the indexed child traversal. It reads
each child's actual position in the candidate term. The parent equalities
then imply the exact descended child equalities through
`eqConstraintsDescend_sound`. No whole-child-forest preservation premise
replaces this traversal proof.

`process_exact` composes this result with the completed local narrowing loop.
`run_exact` proves the complete caller by execution-bound induction.
`public_exact` starts with the source empty inherited constraint. It proves
that every complete term is accepted after a completed pass if and only if
it was accepted before that pass. `fixpoint_exact` proves the same result
for every completed repetition of those passes to an identity fixed point.

`loop_replay`, `process_replay`, and `run_replay` prove that every larger
execution bound returns the same completed result. Bounds instrument the
unbounded source recursion. A failed instrument run does not prove that
the source language is empty or that the source cannot terminate.

The local source contracts remain explicit. Ordinary view rows must describe
their node language. `modify` receives the original node and retains the
complete rebuilt row language. This permits the source unchanged-edge fast
path. Stored normalized classes must be active, and the full stored guard
must imply those equalities. Binder rebuilding must preserve its least
language; `BinderLanguage.cleanup_exact` and the substitution models provide
the semantic components of that adapter. Sparse path operations, interned
row readback, memo storage, and the runtime binder reconstruction remain
separate representation contracts.

This module does not prove general termination of either the local equality
fixed point or repeated whole-node passes. It closes the inherited caller's
preservation obligation for completed execution. The pinned Lean build
passes. No Haskell source changed.
