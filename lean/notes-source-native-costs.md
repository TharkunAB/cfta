# Cost heaps through actual class queries

Proof checkpoint `09cfb640`, source main `525d722e`. The starting checkpoint
is `a8bbe9b5`. The optimized interned core and all earlier proofs remain.
This proof closes the cost-retention gap in the existing supported-query
interface. It does not prove the complete current caller.

The later [reached-prefix proof](notes-source-lazy-class-prefix.md), checkpoint
`3ca8c0c4`, now derives intermediate scan readiness and sound early rejection.
The proposed next prefix target below retains this note's historical scope.
Global memo composition, source entry extraction, fallback, and runtime
transfer remain separate caller work.

## Stored costs and native execution

CostHeap records weighted free-reference readback for each stored Mu payload.
It is separate from a runtime complexity bound and sampling weights.
`SourceRecursiveIntersectionCostEffects.optionalBinder` retains this heap
through each actual optional-binder outcome. The proof uses the actual
maybeMu implementation and its source construction theorem.

`SourceRecursiveIntersectionNative.Bounds.cost_heaps` follows actual native
evaluation. Ordinary work adds no Mu records. Optional binders derive the
new record invariant. Direct calls, completed hits, started requests, and
completion frames retain the exact returned constructor heap.
`done_cost_heap_of_ranges` uses actual completed execution and WordRanges.
`SourceEqualityNativeScoped.Step.cost_heap` specializes this result to the
actual scoped request. It needs available operands and initial IdleReady
and CostHeap. It needs no closedness or final-heap premise.

## Exposure, projection, and tasks

`SourceEqualityExposureCosts.collect_verified` and `nodeEdges_verified`
retain SemanticReady, CostHeap, and both constructor histories at every
bounded reader outcome. A completed read derives resident rows. Inputs can
be open. The Mu fallback starts from the actual returned unfold heap and
revisits the original value, as the source does. No generic growth-only
cost preservation law is assumed.

`SourceEqualityProjectionCosts` retains both heap invariants through actual
Read, ReadAll, Head, Union, Project, ProjectRows, and Forest graphs. Selected
children derive availability from resident rows. Old values pass through
the actual histories. These effect results do not require closed inputs.
They do not assert termination, language completeness, or closed output.

`SourceEmptinessClassFoldCosts` retains costs through actual plain operands,
closed-forest Fold, and Seeded. `SourceEmptinessDecisionCosts` follows actual
task Force, Expose, Run, and Decision. Captures leave the native state intact.
The empty, absent-key, and fixed-point decision branches all retain costs.
Completed exploration remains explicit. No field or language premise is
needed for the decision cost theorem.

## Readiness for the next gate

`SourceSecondaryGateQueryCosts.fold_costs` and `seeded_costs` use the existing
anchored PathSupport interface. This interface derives closed results and
semantic readiness without closing unrelated original children. The new
cost proofs follow the same actual projection and native schedules.
The seeded rotation remains rest ++ [seed].

`seeded_decision_ready` composes actual Seeded and Decision receipts. It
derives final IdleReady, CostHeap, the older gate Ready, Keeps, and normalized
physical fields. It covers either decision answer, including false followed
by a fresh gate. SemanticReady supplies the other older Ready fields.
The final cost or gate invariant is not supplied as a premise.

Anchored support, current original availability, initial costs and fields,
and growth from the fixed gate anchor remain explicit. A false forest gate
alone does not exclude root []. The previous refutation proof derives proper
paths under ClassSat. This theorem does not replace that argument or prove
unconditional readiness of the complete class scan.

## Current primary class receipts

`EndpointMemoGateClasses` adds enabled primary PathTrace and ClassTrace,
exact finite-worker correspondence, uniqueness, and three-family PathReads
and ClassReads. lift_path/lift_class retain exact constructor effects and
memo tables. complete_class derives finite stable class execution from a
certified input. True paths omit the remaining class suffix. This proof
does not force a complete primary partition before a successful query.

## Next target and limits

Model the reached lazy original-class prefix in current Equality/Operations.
Primary clear retains its original selected record. Primary blocked runs
secondary. Secondary blocked skips the query. Secondary clear runs actual
Seeded and Decision. False continues; true stops before later primary calls.
First derive stopped-record membership and apply refutes_decision. Derive
reached readiness from actual effects. Do not hide it as a caller invariant.

Retain all three gate memo families. Actual projection and native queries
can call global unfoldOuterRec. Their unfolding receipts and saved-entry
coherence across growth still need composition. Native node/edge memo tables
are distinct from this global unfolding memo.

General native, fold, exploration, caller, and fixed-point completion remain
open where recorded. Actual WordRanges, newer checked allocation transfer,
GHC lazy row demand and sharing, fallback, waiting counts, template exclusion,
broader APIs/runtime, and all separate Sized contracts remain open.

## Validation and preservation

The pinned full audit passes 2,055 jobs and 52,039 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Log: `/tmp/mcfta-native-cost-audit-20261015.log`.
Nine new proof modules and two additive Audit imports contain the change.
All older proof definitions and all four Haskell package trees are unchanged.
Unchanged Haskell checks were not repeated.

The starting snapshot has 2,714 files. The closing snapshot has 2,724 files:
`/tmp/mcfta-native-cost-checkpoint-20261015-2020/`.
The script is `/tmp/mcfta-preserve-native-cost-20261015.py`.
All earlier proofs, counterexamples, repairs, marked drafts, stashes, and
other worktrees remain. New source copies, probes, and the marked task-cost
draft remain under `/tmp/mcfta-native-cost-*` and in the closing snapshot.
