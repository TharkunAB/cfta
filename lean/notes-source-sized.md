# Exact Sized queries on the explicit graph

Updated: 2026-10-13 22:32 CEST.

The later main theorem, liquid repair, PMF/sampling proofs, and current
source representation bridges are in
[the continuation note](notes-sized-liquid-probability.md).
The Sized repair validation below records the earlier 21:56 checkpoint.

The continuation starts at `f8a3d48`, on upstream `2200117`.
`git pull --ff-only origin microcfta` reported that upstream was unchanged.
The backup branch is `backup/formalization-before-sized-resume-20261013-2123`.
All earlier proofs, counterexamples, repairs, and marked drafts remain.

## Two rank-order defects and the repair

The former optimized `sized` branch called `fromFTA` and then the cyclic
interned import. That path could return a different sequence from
`sizedReference`, although both languages were equal.

1. `fromFTA` trims dead transitions. A removed transition can reverse the
   canonical order of two child states. The retained fixture gives reference
   order `f(z(k)), f(m(k))` and former optimized order `f(m(k)), f(z(k))`.
2. Interning removes duplicate transitions. A second fixture is unchanged by
   trimming, but removing a duplicate leaf edge reverses its canonical child
   order. Its four root terms then receive different class ranks.

`SourceSizedDispatchCounterexample` checks both canonical-order boundaries.
The native fixtures are `repro/SizedDeadEdgeOrder.hs` and
`repro/SizedDuplicateOrder.hs`. Each retains the former import path and
compares it with the repaired path and the reference.

Local repair `ea73724b` supplies the original sorted rows directly to the
existing `Table.tableIndex` and `Table.tablePosition`. A finite synchronous
product checks whether two alternatives share a term. If the graph has a
constraint or overlapping alternatives, dispatch uses the reference.
The interned core remains unchanged. This implements the explicit query
boundary selected by ADR 0004.

The product table can contain a quadratic number of state pairs. It also
contains the compatible pairs of their transitions. Haskell evaluates its
shared minimum-size computation only when the overlap scan needs child
productivity. No performance bound or benchmark improvement is claimed.

## Checked contracts

| Modules | Result |
| --- | --- |
| `SourceSizedCandidates` | The actual reversed-child worker equals the ordered nested product. Left-size splits ascend. Every child query has a smaller node count. |
| `SourceSizedReference` | The finite recurrence satisfies the source table equation uniquely. It retains the first occurrence of each term. Membership is exactly guarded acceptance and node count. A finite evaluation certificate has nesting depth at most size plus one. |
| `SourceSizedEqualities`, `SourceSizedTrimGuards` | Path traversal requires every path to exist. The worker includes the explicit Bottom shortcut. A successful residual scan on structurally trimmed rows suffices for the original root language. Residual guards on discarded rows need no positivity assumption. |
| `SourceSizedQueries`, `SourceSizedReferenceAPI` | Counts and both natural and signed inverse laws use one distinct class sequence. Invalid sizes and ranks are rejected. Finite prefixes are complete, distinct, and ordered by node count. Empty classes do not stop later classes. |
| `SourceSizedRows`, `SourceSizedPreprocessing` | Canonical refinement finishes on the finite validated state domain. Sorting preserves the original guard scans through trimming. The public dispatcher has the exact reference API, original guarded language, and residual error. |
| `SourceSizedPublicContracts` | The public query result has finite class evaluations, exact counts, and complete, distinct size-major enumeration. |
| `SourceSizedDecidedFilter`, `SourceSizedDecidedTable`, `SourceSizedDecidedExecution` | Finite size and state folds use the frozen smaller-size table. The first Unknown in size, state, and candidate order retains its original constraint and term. Finite external evaluations give a finite execution. |
| `SourceSizedDecided`, `SourceSizedDecidedTrim`, `SourceSizedDecidedOrder`, `SourceSizedDecidedQueries` | Successful decided tables have the exact original ordered reference classes through the bound. Classes above the bound are empty. Both rank inverses and size-order laws follow. Nonpositive bounds make no evaluator calls. `SourceSizedDecidedPublic` includes actual canonical preprocessing and original trim keys. |
| `SourceSizedDecidedOperational` | Every successful relational trace has the exact original language and canonical class order under per-call adequacy. Repeated calls may return different verdicts. Finite per-call result witnesses give a finite bounded result. Errors retain the first actual Unknown after successful size, state, and candidate prefixes. |
| `SourceSizedDispatchGraph`, `SourceSizedDispatcher` | The product-minimum scan derives unique runs. Both dispatch branches return the same complete query record and residual error as the reference. Optimized bottom-up ranks agree with first-occurrence reference ranks. |

`SourceSizedDispatchRows` retains a conditional proof for the former interned
adapter. The repaired `sized` path does not need that adapter theorem.

## Related source changes

`SourcePlanPositions`, `SourcePlanPartition`, and `SourcePlanScale` now include
positive `PlanScale`. Scaling preserves member ranks and values. It multiplies
node counts and preserves the exact rank partition. Nondivisible sizes have
zero count. The source quotient selector is correct on valid counted classes;
the checked invalid-input example shows why that premise is required.
`CompactGroups.childGroups_nonempty` supplies the positive group factor.

`BoundedPruningFix` proves the signed `fixWithin` caller, its call limit,
invariant preservation, and finite execution under a per-call termination
contract. `BoundedPruningCaller` covers the current edge remainder and local
recursive-node revisits. A recursive body starts a new budget of 64. Only the
direct revisit receives the decreased budget. These results do not prove that
every body callback, solver call, or interned reconstruction terminates.

## Validation and boundaries

The generator suite passed 206 examples with two temporary regression cases.
The permanent suite is unchanged at 204 examples. The temporary patch is
`/tmp/mcfta-resume-20261013-2123/sized-regressions.patch`.
The two native fixtures and both Lean counterexamples are committed.
Fourmolu and cabal-gild checks passed in Nix. The Cabal pass marker is
`/tmp/mcfta-sized-20261013-generator.log`; the direct test output reported
206 examples and zero failures.

The aggregate audit passes 1,084 jobs and 38,123 theorem dependency checks.
It permits only `propext`, `Classical.choice`, and `Quot.sound`. Its final log is `/tmp/mcfta-main-20261013-final-audit.log`.
No new production test case was committed.

The finite graph, list, comparison, and integer models are handwritten source
ports. There is no verified Haskell extraction. Concrete Map and Set storage,
lazy heap sharing, host allocation, machine-size conversions, and resource
exhaustion remain representation boundaries. Constraint-cache normalization
and lawful state/symbol comparison are explicit input invariants. The reference evaluation bound
counts nested class calls, not primitive runtime instructions.

The decided path requires semantically correct Yes and No replies on each
completed invocation. Unknown remains an error. The operational proof permits
different verdicts on repeated queries and needs no fixed reply function.
Finite per-call result witnesses give existence of a finite bounded result.
This contract does not assert unconditional termination of an external solver.
The earlier deterministic reply-function models remain useful special cases.

General repaired constructor completion, open nested Mu rebuilding, whole
recursive pruning completion, and the retained equality drafts remain open.
They do not block the direct explicit-graph Sized queries.
