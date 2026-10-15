# Sound early rejection through reached original classes

Proof checkpoint `3ca8c0c4`, source main `525d722e`. The starting checkpoint
is `a421f9cd`. Full library scope stays active. The optimized interned core,
older constructor and equality proofs, and separate Sized contracts remain.

The later [query memo proof](notes-source-query-memos.md), checkpoint
`60a8d3eb`, now derives actual projection/exposure memo receipts and ordered
entry laws from cached original record readback. Earlier next steps below
retain this note's historical scope. Native global-event instrumentation,
whole-query/Scan memo composition, concrete entry extraction, and fallback
remain open.

## Exact reached schedule

`SourceEqualityLazyClassPrefix.Scan` records the current caller schedule.
Each primary class uses the enabled endpoint policy. A false primary answer
selects that original record and continues. A true primary answer runs the
secondary gate. A true secondary answer continues without a query. A false
secondary answer runs actual Seeded and Decision. A false decision continues.
A true decision stops immediately. There is no receipt for the remaining
original classes. Exhaustion retains selected records for the separate fallback.

The graph passes the exact returned constructor heap through advanceHeap.
The scoped native domain and node/edge memo tables stay in the same state.
Actual seeded queries retain their rest ++ [seed] schedule. They do not use
the row-analysis foldr1 schedule. No complete primary partition is supplied.

stopped_member proves that the stopped class belongs to the original list.
selected_sublist retains original selected order and multiplicity. The graph
does not replace original records with a newly computed set of classes.

`EndpointGateClassModes` proves enabled/disabled equality for actual meets
and classMeets workers at every fuel amount. Enabled is the current primary
worker. Disabled is the exact free-reference secondary worker. These
equalities retain all outcomes and returned heaps, not only Booleans.

## Derived intermediate invariants

`SourcePrimaryGateEffects` follows current enabled Node/Child/Edges/Path/Class
traces. Endpoint descendant reads do not change the constructor heap. Actual
stored unfolds retain SemanticReady, CostHeap, physical annotations, and both
constructor histories. No closed input or final-heap premise is needed.

`SourceSecondaryGateQueryReady.queried_effects` starts from an actual false
secondary ClassTrace. Seeded starts in the same native state advanced to that
exact anchor. ClassSat for an active class supplies proper paths and anchored
support. The completed query then derives final IdleReady, costs, fields,
Keeps, and original availability. ClassSat is sufficient; this effects result
does not need an accepted-term premise. refutes_decision derives the exact
true-query refutation from initial invariants and independent acceptance.

`SourceEqualityLazyClassSoundness.primary_advance` and secondary_advance
derive next-call invariants after actual gate effects. verified follows the
entire reached Scan. Under independent acceptance and satisfaction of all
active original classes, it derives no early rejection, final IdleReady,
CostHeap, normalized fields, Keeps, and retained original Values. Intermediate
gate/query readiness is derived. It is not supplied at each reached call.

stopped_refutes excludes every independently accepted original forest that
satisfies all original active classes when Scan stops at a true decision.
It uses no semantic emptiness oracle, whole-original-forest closedness,
static path domain, or completed fallback premise.

## Remaining correspondence

Scan is a source-operation receipt graph. It does not yet prove the exact
GHC demand and sharing of partition/any. Its input is an explicit ordered
class list with Active in the soundness theorem. Connect the original
unsafeSubsumptionOrderedEclasses and normalized source constraints to that
entry list. The initial native readiness, costs, fields, and original Values
remain explicit. Supply them from the complete caller construction.

Global gate unfolding, predicate, and descendant memo families need full
Scan composition. Existing individual gate receipts remain. Projection and
native queries can call global unfoldOuterRec; derive their actual memo
receipts and saved-entry coherence across growth. Native node/edge memo
tables retained by Scan are distinct from those global gate families.

The selected fallback still needs requireAll, evolving-forest class reduction,
and empty propagation. General native, exploration, caller, and fixed-point
completion remain open where recorded. Actual Step WordRanges and completed
Decision exploration remain premises. Newer checked allocation transfer,
progressive lazy rows, original child forcing, waiting counts, template
exclusion, broader APIs/runtime, and separate exact Sized contracts remain.

## Validation and preservation

The pinned full audit passes 2,060 jobs and 52,058 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Log: `/tmp/mcfta-lazy-prefix-audit-20261015.log`.
Five new modules and two additive Audit imports contain the proof change.
All older proof definitions and all four Haskell package trees are unchanged.
Their unchanged Haskell checks were not repeated.

Start: `/tmp/mcfta-native-cost-checkpoint-20261015-2020/` (2,724 files).
Closing: `/tmp/mcfta-lazy-prefix-checkpoint-20261015-2030/` (2,730 files).
Script: `/tmp/mcfta-preserve-lazy-prefix-20261015.py`.
All prior proofs, counterexamples, repairs, marked drafts, stashes, and other
worktrees remain. New logs, probes, and frozen sources remain in the closing
snapshot. Weekly allowance is 85%. Stop owned work at 1% or less.
