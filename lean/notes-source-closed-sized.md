# Complete Sized queries from original closed source expressions

Updated: 2026-10-14 23:43 CEST.
Proofs: `dd240eb6` and `0e8b2265`. Source base: `origin/main` at `f201deda`.
Repository: `TharkunAB/cfta`. Publish checkpoints on `formalize`.

## Actual cold reference and optimized paths

The source composition is `Data.CFTA.Interned.toFTA`, followed by either
`Data.CFTA.Sized.sizedReference` or `Data.CFTA.Sized.sized`. Both paths use
the actual normalized validated cold table. The existing optimized interned
construction core remains in place.

`SourceSizedNormalizedConstraints.normalized_lookup` proves literal complete
raw lookup equality after map normalization. `Trace.normalized_constraints`
then derives every query-row annotation from the initial edge invariant
through the actual repaired traversal. Original checked syntax establishes
that invariant. No final rowwise annotation certificate is supplied.

`SourceFreshOrdinarySizedEntry.queries_reference` identifies the full actual
dispatcher result with the reference result. This includes residual-guard
errors and all four query fields. `Execution` retains physical open checks,
actual cold traversal, and public FTA validation before either Sized path.
`Execution.change_dispatch` changes only the selected query path. It proves
the identical complete result and identical final constructor cache.

`SourceFreshOrdinarySizedEntryCorrect.complete_both_exact` derives both
actual executions with one common result and cache. Successful APIs satisfy
`SourceSizedApiLaws.Exact` at the independent guarded language of the original
physical root. Conversion arity errors and Sized residual-guard errors keep
separate channels. `constructed_complete` derives every internal premise
from actual checked closed construction. It supplies no validation success,
final row metadata, or language equation.

The exact specification includes finite class evaluations, exact distinct
accepted terms per node-count size, counts, signed invalid-position rejection,
accepted-term rank coverage, distinct size-major prefixes, and both signed
rank/unrank inverse directions. The existing canonical and finite product
minimum proofs supply the dispatcher. No new product or scan premise is used.

## Original source expression to complete queries

`SourceClosedSized.reference_and_dispatch` starts with the original source
expression and checked equality annotations. It invokes the existing general
closed construction completion theorem. The theorem derives the actual value
and cache, public conversion, and both query executions. No supplied finished
construction equation remains. Both paths return the identical complete result.

Successful queries denote `InternedGuardedSyntax.evaluate` for that original
expression. This is its independent guarded least language. The existing
closed language theorem connects the actual returned value to the expression.
The query statement no longer depends on a caller-supplied physical root.

`SourceClosedSized.solver_decided` gives the corresponding composition for
actual encoded bounded solver execution. It derives construction and uses
the original expression's independent guarded language under the ambient
solver meaning, conjoined with the signed node-count bound. Finite external
attempts and correct responses remain explicit contracts. Conversion errors,
raised failures, Unknown, actual occurrence work, and successful query records
retain the previously proved source behavior.

## Validation and preservation

The four new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate audit passes 1,564 jobs and checks dependencies of 44,406 theorems.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-source-closed-sized-20261014-audit.log`.
Only the old unused `inputs` warning remains. No production Haskell code
changed. No previous proof module changed except audit imports. All fixtures,
marked drafts, repairs, backups, stashes, and other worktrees remain.
Snapshot: `/tmp/mcfta-source-closed-sized-checkpoint-20261014-2343/`.
It saves all 1,945 Lean-tree files and four root documents.

## Next constructor and equality target

The Sized reference, optimized, and solver-decided compositions now reach
the original source-expression language at the stated source-model layer.
Do not repeat construction completion, cold traversal, row validation,
canonical dispatch, or query inverse proofs.

Resume the general constrained-recursion gate for opaque probes. Read the
last section of `notes-gate-unfolding-rank.md`, `InternedReachableGateRank`,
and `InternedSourceRankStutter`. The reachable rank still requires shallow
Mu records. The later pure-probe result does not cover opaque probes.
First replay the retained rank example with the repaired
`InternedFreshOrdinaryConstruction` and its stored executor. Distinguish
that executor from the older `InternedNestedConstruction` example before
using a counterexample or candidate measure for the current source.
Cached maximum Mu depth and an unqualified strict head-rank claim are not
established general source measures. Preserve the checked unary ancestor
root theorem and its archived draft; do not resume the already completed
edit or unary root-loop proof from an older note.

Concrete containers, lazy scheduling, primitive resources, external solver
behavior, and verified Haskell extraction retain their existing boundaries.
Push completed checkpoints regularly. Do not deploy, send messages, or post
to the board. Check allowance and stop all work at 1% remaining or less.
