# Inherited equality reduction

Both filtered Mu probes now have an explicit physical heap invariant. Actual
source and native execution, reads, merging, targets, shared edits, and complete
guarded passes preserve it. The returned heap supplies exact outer Mu execution.
Next use mutually recursive completed outer graphs to obtain actual child
induction hypotheses, then prove bounded worker agreement and replay. Carry
the probe invariant explicitly; current IdleReady does not contain it. Read
[the current note](notes-filtered-probes.md). This paragraph supersedes older
probe propagation and unrestricted callback targets in this note.

The actual outer worker, ordered rows, modifyNode fast path, and cached Mu
reconstruction are now checked. Successful outer steps derive their local
language and scope conclusion. The smaller recursive callback and reached
physical checks remain explicit. The next target is probe-invariant propagation
and traversal-bound induction. Read [the current note](notes-partial-node.md).
This paragraph supersedes older outer traversal and Mu targets in this note.

Actual inherited/local physical payload combination and trie descent are now
proved. Indexed children derive their own obligations and preserve actual
scopes and language under an explicit recursive-node induction hypothesis.
The concrete native edge step composes with this inherited continuation.
The outer node/row worker and actual Mu reconstruction still need to derive
that hypothesis. Read [the current note](notes-inherited-edge.md).

`PartialReductionCaller` models the schedule in
`Data.CFTA.Equality.Operations.reducePartially'`. It uses the previously proved
`EqualityReduction.pass` worker once for each edge. This matches the
single-pass change merged in `microcfta` at `bbeb7be`. The caller then combines the
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

`process_exact` composes this result with the single local narrowing pass.
`run_exact` proves the complete caller by execution-bound induction.
`public_exact` starts with the source empty inherited constraint. It proves
that every complete term is accepted after a completed pass if and only if
it was accepted before that pass. `fixpoint_exact` proves the same result
for every completed repetition of those passes to an identity fixed point.

`process_replay` and `run_replay` prove that every larger traversal bound
returns the same completed result. `loop_replay` remains a separate result
for callers that explicitly iterate a local pass. Bounds instrument the
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

This caller has no local equality fixed point. General termination of
explicit edge fixed points in pruning and repeated whole-node passes remains
open. It closes the inherited caller's
preservation obligation for completed execution. The pinned Lean build
passes. No Haskell source changed.
