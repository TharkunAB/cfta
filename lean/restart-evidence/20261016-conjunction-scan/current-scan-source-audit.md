# Current conjunction memo at the class scan

Read-only audit, 2026-10-16 06:55 CEST. No proof or Haskell source was
edited. No build or Haskell probe ran. Reviewed source hashes are in
`current-scan-reviewed-sha256.txt`.

## Literal source order and early stop

`Equality/Operations.hs:206–213` checks both physical empty payloads,
then combined contradiction, then `any emptyBelowEnd refused`. The
otherwise branch alone demands required children and class narrowing.
The shared `partition` at line 213 uses `Data.List.partition` (import at
line 19). It partitions the ordered ORIGINAL own classes, not the combined
classes. Every gate reads `origNs`.

The selected partition is not evaluated in full before the refused `any`.
The lazy refused list drives the primary predicates in original class
order until the first refused class is available. That class then runs
its secondary predicate. A true secondary predicate makes its
`emptyBelowEnd` false without a query. A false secondary predicate demands
the query and the current emptiness memo. A true emptiness answer stops
the refused `any`. It demands no suffix primary predicates, suffix
secondary predicates, suffix queries, `requireAll`, or class narrowing.

Primary-false classes encountered before the stopping refused class are
selected occurrences in a reached prefix. They do not constitute the
full selected partition. On rejection the source does not use that
partition. If no refused query rejects, traversing the refused list to
its end classifies every original class. The selected partition then is
the full stable primary-false subsequence. A new graph must distinguish
these two claims. It must not supply a completed full partition before
the refused scan. This is a source demand analysis, not a GHC allocation
or thunk-sharing adequacy proof.

Within a refused class, lines 219–224 put the secondary gate before the
query. Paths use the actual ascending `Set.toList` order. Lines 228–230
define `intersectList (n:ns) = foldr intersect n ns`. For paths
`[p0,p1,p2]`, the expression is `p1 intersect (p2 intersect p0)`.
The existing `seededPaths` rotation `[p1,p2,p0]` and head projection,
tail fold, native request schedule match this completed resident
dependency schedule. No `mergeAlternatives` occurs in this query.
The later class narrowing has its separate merged-other-path schedule
(236–240). Neither a left fold nor an eager projection pass preserves
the literal request order and allocation history.

## Current decision boundary

`Enumeration.hs:588–640` uses the global `provablyEmptyCache`, with lookup
outside the body. A miss has the free-variable shortcut before demanded
exploration. Closed inputs use a budgeted conjunction worklist, literal
matching edge tuples, allocated equality accessors/combinations,
row-major path requirements, canonical node-identity conjunctions, and
the least Boolean fixed point. The budget is 1000 (642–644). Budget
exhaustion makes unexplored conjunctions unknown; it does not bound all
resident read or runtime forcing work.

`SourceCurrentConjunctionMemo.Call` (23–28) is the correct existing
completed hit/miss component. `finite` (83–90) derives the actual call,
physical `Effects`, final Boolean memo correctness, conservative answer,
and old-entry retention from initial physical readiness, query
availability, and initial memo correctness. No supplied completed
decision or final invariant is needed. Reusing the old immutable Memo,
Correct, and AnswerSound TYPES is legitimate. Reusing the historical
`SourceCurrentEmptinessMemo.Call` as an execution is not.

`SourceCurrentEqualityClassScan` still has that old Call at lines 45 and
53. Its Seeded uses the old scoped native engine. It therefore cannot be
the new source Scan by changing a theorem invocation or only its comments.
`SourceCurrentClassPrefixCompletion` correctly stops before this changed
body. Its finite theorem also uses old native Seeded/range receipts;
it does not derive current checked allocation effects by itself.

## Minimum new relation

Use full `SourceEqualityNativeDemand.State width` at each source point.
Keep its native heap, domain cache, both native cell tables, and equality
operation cache. The Boolean memo is a separate input/output parameter.
Use new allocated Operand/Fold/Seeded graphs. Operand stores the actual
Forest projection and its returned heap; the equality state is unchanged.
Fold stores head projection, tail fold, then actual CHECKED empty-domain
`requestNode` execution at the tail's full returned state. Seeded rotates
the original seed to the end, with the exact empty fallback.

The new Scan needs only five branches: nil, selected, skipped, continued,
and stopped. Their primary/secondary predicates match the existing current
trace constructors. The queried branches store the new checked Seeded,
then `SourceCurrentConjunctionMemo.Call budget memo query
(physical queried) answer physicalAfter saved`. Resume at
`advancePhysical queried physicalAfter`, retaining both returned state
components. Only the false answer continues to the class suffix.

Prefer an outcome `clear selected | stopped originalClass`. If a separate
selected list is retained on a stopped outcome, name it selected-prefix
and prove only reached-prefix/sublist facts. Full selected-partition
equivalence belongs to `clear`. Preserve occurrence order and multiplicity
in the graph even when source normalization later discharges duplicates.
Structural proofs are list induction: stopped original member, no suffix
trace after stop, selected-prefix sublist, and full clear subsequence.
Do not require a completed selected partition to construct a stop.

## Derived physical finite route

`SourceCurrentAllocatedGateFields.primary_complete/secondary_complete`
(66–85) derive finite gates with loaded fields and the SAME equality
state. `false_class_path_complete` (167 onward) and `forest_complete`
(154 onward) derive closed available selected projections at the actual
returned anchor. They require proper selected paths, not a closed whole
original forest. Active satisfied classes derive proper paths in semantic
soundness; normalized entry can derive them separately for completion.

For each new checked native fold leaf, the precise existing endpoint is
`SourceCurrentAllocatedNativeScopeCompletion.initial_complete:650–674`.
It takes current Good, Scoped, SemanticReady, Idle, both Original
operands, current availability, both `free=[]`, and actual checked
WordRanges. It DERIVES NodeScope and independent Completes at this current
heap (665–671). It does not accept a completed body, desired result law,
or final invariant. It preserves the SAME actual warm checked state.
The theorem does not initialize empty tables despite its name.

Original is still an explicit premise there. For a projected closed
available value or an already closed native tail, it follows from
`SourceRecursiveIntersectionOriginalOutput.closed_original:91–96`, using
current coherence from Good. This conclusion applies only with those
closedness and availability witnesses. It is not an assertion about
arbitrary generated results. The endpoint returns actual availability,
closedness, final Good, Scoped, SemanticReady, Idle, extension, physical
trace, and equality-operation growth.

The constructed trace supplies its own physical input plan through
`PhysicalTraceCompletion.Trace.plan:80–88`; `PhysicalExecution.through_heap`
(224–235) supplies the plan used by actual cost preservation. Thus initial
CostHeap can be retained without a final-cost premise or old-engine
replay. Induction on the finite seeded path list can apply this at each
current leaf heap. That NEW fold integration is not already proved.

Gates, projections, and current conjunction calls advance the machine
with their actual returned heaps. Native domains and both cell tables
stay unchanged during these non-native operations. Their validity follows
from `PhysicalCache.advance_valid:85–90` and the derived machine Extension.
Scoped retention follows from `ScopeCache.advance_scoped:95–97`. Good
uses the returned loaded Fields and operation Valid. Native leaves can
then use the physical finite endpoint without a fixed language model.

A new finite Scan can use a range-only plan indexed by actually reached
prefixes, analogous to existing WordRanges and FoldRanges. Such a plan
must contain key checks only. It must not contain a future finite query,
final Good, final Fields, final cache correctness, or local semantic
answer. Induct over actual projections, tail folds, and the class list;
derive all these invariants and the new memo call at each returned state.

## Separate semantic composition still needed

To refute a satisfied class, the seeded result must retain its common
accepted subtree. Current projection inclusion supplies each operand's
acceptance without closing unrelated siblings. Each actual checked native
leaf then needs at least common-input acceptance implies result acceptance
for the two closed physical operands. Compose that law through the same
ordered Fold. A true new memo answer excludes the resulting subtree via
its derived AnswerSound. Then Scan soundness is list induction over the
original active satisfied classes. No arbitrary accepted-row or final
rejection oracle is needed.

Physical completion and scope alone do not prove that inclusion law.
`WarmQuery.query_complete:72–123` supplies an exact law only in one fixed
source model with original operands available and valid in that source.
New projection nodes and generated fold tails are not automatically
available in that earlier source or valid in its fixed model. Replacing
the source model while retaining its Contextual cells needs a proved
model/heap-extension transport or a stronger model-independent warm
semantic invariant. It is not justified by physical residency alone.
The per-current-heap Scope completion route avoids this issue for finite
physical completion; it does not solve semantic transport.

`SourceCurrentAllocatedQueryMemo.finite_after_query:145–176` remains an
older CONDITIONAL bridge. It takes actual done and a rich reached input
plan with semantic finish obligations plus Provenance.Valid. It must not
be advertised as supplying new general query completion or used to hide
an own-result law in a plan. New native semantic completion and cache
admission must discharge those obligations, not copy them to Scan inputs.

Finally, the conjunction Memo currently models only the fourth Boolean
family and physical effects. It does not give receipts for all global
unfold/predicate/descendant memos. Exposure can unfold; unchanged query
tables or global-call silence must not be asserted from physical Keeps.
Concrete key capacity, host Map/IntMap behavior, lazy publication,
concurrency, and whole constrained outer-caller termination remain
separate source/runtime bridges.
