import MicroCFTA.SourcePruningEnumerationTraversalPrefixProjectionHeap

/-!
# Projection heaps at actual stopped child traversals

The completed prefix derives the current context for the stopping child.
The stopping child's outer successful observation retains its reached heap.
Its raw Option result and cache candidate remain unrestricted.
-/
namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Fragment × Core))
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {bits : Nat}

/-- An actual stopped outer success retains projection at its exact returned native caller. -/
theorem stopped_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {r n p h k : Nat} {completedPrefix : List Fragment} {result : Option Raw}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries} {outer : Core}
    {waiting : EnumerationWaitingIndex.Waiting} {candidate : Option Cached}
    (observed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k inputs
      beforeCaller before memos.query =
        .stopped completedPrefix (.ok result, afterCaller, savedQueries, outer, waiting) candidate) :
    ProjectionHeap afterCaller.checked.native.machine.heap := by
  obtain ⟨consumed, incoming, bucket, remaining, stoppedCaller, stoppedBefore, stoppedQueries,
    decomposition, trace, stopped⟩ :=
    SourcePruningEnumerationChildTraversal.stopped_trace checkEmpty r n p h k inputs beforeCaller
      before memos.query completedPrefix (.ok result, afterCaller, savedQueries, outer, waiting) candidate observed
  rw [decomposition] at genuine reserved
  obtain ⟨next, final, stoppedRoots, post, querySame, stoppedSafe, stoppedPaths, stoppedCounts,
    _stoppedFlags, stoppedRealized, stoppedGenuine, stoppedFits, stoppedKnown,
    stoppedReserved, stoppedProjection⟩ :=
    trace_prefix_resources_projection_heap trace ((incoming, bucket) :: remaining) seed formulas
      solver inventory roots memos rfl initial safe paths counts flags realized genuine fits reserved
      known originalProjection
  obtain ⟨available, closed, bounded, pending⟩ := stoppedGenuine incoming bucket (by simp)
  have headReservation : Reserved bits (advance seed (cost consumed)) (bucket.length + 1) :=
    stoppedReserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost remaining; omega)
  have actual : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming
      stoppedCaller stoppedBefore final.query =
        ((.ok result, afterCaller, savedQueries, outer, waiting), candidate) := by
    simpa only [querySame] using stopped
  exact (SourcePruningEnumerationChildDispatch.observed_resources_projection_heap
    (advance seed (cost consumed)) formulas solver next stoppedCaller stoppedBefore checkEmpty r n p h k
    bucket incoming stoppedRoots final post.context stoppedSafe stoppedPaths stoppedCounts stoppedRealized
    bounded pending available closed stoppedFits headReservation stoppedKnown stoppedProjection actual).2.2

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
