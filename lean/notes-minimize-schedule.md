# Complete finite minimization schedule

`MicroCFTA/MinimizeSchedule.lean` models the control flow of
`Data.CFTA.Refinement.Minimize`. The model uses ordered finite tables, stable
transition addresses, and syntactic constraint identifiers.

The executable model includes:

- One-direction similarity inference, including the converse of an unknown query.
- First-dominator selection, transitive resolution, and directed-cycle errors.
- Original transition addresses retained throughout table mutation.
- Every source skip condition in `applyStep`.
- Copies that redirect all occurrences of the removed child state together.
- Alternative deduplication and deletion of only the selected transition.
- Polarity-sensitive guard reads, path-prefix graph descent, and containing states.
- The unconstrained-representative check.
- Structural productivity, redirect dependencies, representative survival, and root fallback.
- Final unproductive-transition removal and validation outcomes.

## Complete-schedule root nonemptiness failure

`full_schedule_loses_all_root_terms` proves the central implementation finding
through the executable schedule. It does not merely assume a rewritten graph.

The initial state has the accepted leaf `b` and a rejected `f(a)` alternative.
The latter carries `Satisfies [] false`. A separate child state accepts `a`.
The supplied similarity says that `a` represents `b`.

The complete schedule removes `b`. The rejected `f(a)` alternative keeps the
root structurally productive. The representative `a` remains accepted at its
child state. The graph read check allows the root observation. All schedule
fallback checks pass, and the output root accepts no finite term.

The theorem proves all of these facts together:

1. `minimize` returns the computed output table.
2. The original root has an accepted term.
3. The output representative still has an accepted term.
4. The output root remains structurally productive.
5. The output root has no accepted finite term.

This is stronger than the intended loss of distinct terms during similarity
minimization. It violates accepted-root nonemptiness preservation. The source
fixture in `repro/CurrentFindings.hs` supplies the corresponding real subtyping
oracle and liquid guard. The model uses the exact ground truth of the two
fixture constraints: `Top` accepts, and `Satisfies [] false` rejects.

`full_schedule_not_language_equivalent` separately checks the expected case:
two accepted leaves in one state reduce to the selected representative leaf.
That result follows the documented contract. It is not itself a defect.

## Other checked behavior

The proofs cover original-copy retention, simultaneous child replacement,
known-direction selection, unknown-query errors, and cycle detection.
Complete executable examples cover transitive dominators, longer cycles,
structural-guard rejection, constrained-representative rejection, loss of
structural root productivity, cyclic-guard fallback, and stale snapshots.

## Representation boundaries

The input table supplies addresses after the source's explicit-view conversion.
The model checks address presence and table closure. Symbols, refinements,
and formula payloads use stable natural-number identifiers. Guards use the
source read shapes. A structural scope records the complete paths that a
`Substitute` scope reads. N-ary conjunctions and disjunctions use binary folds.
No SMT call is evaluated by the schedule.

The graph closures use a finite iteration bound of the table size plus one.
On a closed finite table this bounds the monotone set growth. `Productivity.lean`
proves the finite graph fixed-point principles and acceptedness under clear
constraints. A general representation proof connecting every list closure
in this port to those Boolean-set results remains open.

The final recursive-guard validator is a callback with the source's three
outcomes: valid, cyclic guard, and another invalid structure. The port does
not implement the full interned-graph conversion or that validator. The root
counterexample is acyclic, so its valid callback result has no recursive-guard
ambiguity.

The model does not claim that arbitrary source-language subtyping preserves
all observations. The existing `Minimization.lean` proves the local semantic
compatibility conditions. Those conditions and structural productivity do
not repair the complete-schedule root counterexample above.
