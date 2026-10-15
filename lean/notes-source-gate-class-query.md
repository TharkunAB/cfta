# Actual seeded class queries after false secondary gates

Source main remains `525d722e`. The starting checkpoint is `702443fe`.
The checked proof checkpoint is `602b20a7`.
The [gate projection note](notes-source-gate-projection.md) records the
earlier actual projection results. This work transfers those results through
the retained scoped native state and both actual class-fold schedules.
It derives gate-based class-query refutation without a static path domain.
The current whole caller and general completion remain open.

The later [native cost proof](notes-source-native-costs.md), checkpoint
`09cfb640`, now retains costs through the supported actual query and decision.
It derives old gate Ready after either answer. It also adds current enabled
primary Path/Class memo receipts. Earlier proposed cost steps below retain
their historical checkpoint scope. The whole lazy caller remains open.

## Actual scoped path operands

`SourceSecondaryGateScopedProjection.PathSupport` retains the exact natural
witness of each signed source path and its ForestSupport at one anchor G.
`mapped_support` and `path_support_of_false` derive these witnesses.
The empty natural path keeps its explicit closed-forest premise.

`operand_effects` follows the actual Operand.force receipt. forest_verified
derives projection effects. IdleReady.advance then supplies the exact native
state with the returned constructor heap. Both native node/edge memo tables
and the native domain cache remain unchanged. Original availability can
pass to later calls through the returned Keeps and its issued history.

`operand_included` retains accepted selected subtrees for proper paths.
`operand_heap` retains physical annotations in the actual returned heap.
`operand_complete` derives finite projection and the exact advanced state.
Projection itself needs no native WordRanges premise. These native tables
are distinct from the global unfolding memo used by gates and projection.
No theorem here asserts that the global unfolding memo stays unchanged.

## Both actual class schedules

`SourceSecondaryGateClassFold.fold_effects` and `seeded_effects` derive
IdleReady, Keeps, and a closed resident result. Every path uses support at
the same G. Each projected operand, tail fold, and native Step passes its
exact returned state to the next operation. Original Values and Grows G
current.heap remain available for later projections. A native Step receives
the newly derived closed operands. No later cost heap is needed.

`fold_included` and `seeded_included` retain every common selected subtree
of an independently accepted original forest. Actual native conjunction
preserves the common term. Fold projects its head, evaluates its tail, then
intersects. Seeded rotates seed :: rest to rest ++ [seed]. Its empty-list
fallback returns EmptyNode without work. No theorem substitutes a different
schedule or claims GHC demand correspondence.

`SourceSecondaryGateClassFields.fold_heap` and `seeded_heap` preserve each
physical annotation predicate through those actual schedules. Projection
retains annotations. The existing scoped native annotation theorem retains
them through each completed native request. Concrete top and conjunction
constructors derive the normalized field heaps in fold_fields/seeded_fields.
No final field heap is assumed. The newer checked constraint-operation state
remains a separate source bridge.

## Gate-based class refutation

`SourceSecondaryGateRefusedClassQuery.class_witness` derives a strictly
smaller common accepted subtree in the actual seeded result.
`refutes_decision` starts from an actual false secondary ClassTrace, its
initial semantic/weighted readiness and original availability, a completed
actual Seeded receipt, current IdleReady/fields/Values, growth from the gate
anchor, and a true actual Decision. It refutes satisfaction of the original
active class by every accepted original forest.

The proof first assumes ClassSat. Nontrivial plus ClassSat derives proper
paths. Only then does class_anchor supply supported paths for seeded effects,
normalized fields, and the common accepted subtree. Decision.sound excludes
that subtree. No whole-original-forest closedness, static projection domain,
final query-language oracle, or generic semantic emptiness oracle is supplied.
A false forest gate and Nontrivial alone do not exclude []. Moving effects
before the ClassSat assumption would require an unjustified extra premise.

## Next current-caller target

Current Equality/Operations.hs uses lazy partition followed by any over
refused classes. Do not execute the entire primary partition before the
first successful empty query. The next graph should record the reached
original-class prefix and its exact intermediate states:

- Primary clear: retain the original selected record and continue.
- Primary blocked: run the disabled secondary gate on original values.
- Secondary blocked: continue without a query.
- Secondary clear: run actual Seeded and Decision. False continues; true
  stops immediately, without later primary queries.
- Exhaustion: retain selected records for the actual requireAll, class
  reduction fold, and empty propagation fallback.

The first stop theorem should derive membership of the stopped original
record and apply the new refutes_decision. It must not assume an emptiness
oracle or a completed fallback. Keep original record occurrences and path
order. Existing full SourceMemoClassSelection uses the free-only policy and
cannot certify the current enabled primary partition.

EndpointMemoGateTrace currently has enabled Node/Child/Edges receipts.
Add current primary Path/Class and ordered prefix wrappers. Secondary can
use SourcePredicateGateTrace PathReads/ClassReads with the descendant memo
retained. EndpointGateModes.stateful_enabled/stateful_disabled identify the
two exact workers. Retain unfolding, predicate, and descendant memo families.
Actual projections and native queries can call global unfoldOuterRec, so
thread those unfolding receipts and prove saved-entry coherence after growth.

There is a separate readiness gap after an earlier query returns false.
Seeded/Decision retain IdleReady, fields, growth, and issued history. They
do not yet derive the older gate Ready cost heap for the next fresh gate.
Do not infer that heap from Grows. Derive actual preservation or a sufficient
local invariant for the original queried records before claiming complete
caller-state preservation. Record any explicit reached-call premise as a
remaining obligation, not as a proved caller invariant.

The proposed cost proof starts at actual optionalBinder. Rewrite it with
SourceRecursiveIntersectionMaybeMu.maybeMu_eq and use
InternedFreshOrdinaryCosts.build_costs. Follow the existing
SourceRecursiveIntersectionBudgetEffects.optionalBinder proof.
Then adapt SourceRecursiveIntersectionNativeBudgetHeap.Bounds.budget_heaps
to CostHeap. Ordinary work already supplies NoNewMu; optional binders need
the new primitive theorem. Expose Step.cost_heap, then retain it through
Fold/Seeded and demanded Decision work. SemanticHeap already contains the
context and decoded depth heap; SemanticReady also retains coverage.
Together with CostHeap these supply the older gate Ready.
This route is not yet checked. Original Mu Correct facts alone are not
enough for existing execute_costs/hit_costs APIs: reconstructed requests
and new cache hits can lie outside the original input inventory.

Actual Step receipts include native WordRanges. Completed Decision receipts
include the exploration they demand. General native/fold/exploration
completion, checked allocation transfer, GHC lazy sharing, whole caller,
recent waiting counts and template exclusion, broader APIs/runtime, and
all distinct exact Sized contracts remain separate full-library targets.

## Validation and preservation

The pinned full audit passes 2,046 jobs and 51,989 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. The existing unused
input warning remains. No new warning, admission, or axiom occurs.
Log: `/tmp/mcfta-gate-class-query-audit-20261015.log`.

All prior Lean definitions remain byte-identical except one additive Audit
import. All four Haskell package trees match `702443fe`; their unchanged
checks were not repeated. All earlier proofs, repros, marked drafts, external
drafts, stashes, and other worktrees remain.
Start: `/tmp/mcfta-gate-projection-checkpoint-20261015-1953/` (2,709 files).
Closing: `/tmp/mcfta-gate-class-query-checkpoint-20261015-2002/` (2,714 files).
Script: `/tmp/mcfta-preserve-gate-class-query-20261015.py`.
Weekly allowance is 86%. Full scope remains active.
