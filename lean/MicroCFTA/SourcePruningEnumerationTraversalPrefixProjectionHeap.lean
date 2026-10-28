import MicroCFTA.SourcePruningEnumerationTraversalProjectionHeap

/-!
# Original resources through an actual ordered child prefix

The trace supplies the consumed child calls at their actual returned caches.
Each call derives the next native context and full query memos.
The untouched suffix retains its original admissions and reservation.
-/
namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
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
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {bits : Nat}

/-- An actual consumed prefix derives all current admissions for the untouched suffix. -/
theorem trace_prefix_resources_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {beforeCaller afterCaller : Caller (bits + 2)} {before after : Cached}
    {queries savedQueries : Queries} {fragments : List Fragment}
    (trace : SourcePruningEnumerationChildTraversal.Trace checkEmpty r n p h k inputs
      beforeCaller before queries fragments afterCaller after savedQueries)
    (rest : List (Node × List Suspended)) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (roots : Nat → Nat) (memos : Memos) (querySame : memos.query = queries)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ value bucket, (value, bucket) ∈ inputs ++ rest →
      Available beforeCaller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost (inputs ++ rest)))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap) :
    ∃ (next : Inventory) (final : Memos) (afterRoots : Nat → Nat),
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Safe after.core ∧ Roots after.core.representatives afterRoots ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      (∀ value bucket, (value, bucket) ∈ rest →
        Available afterCaller.checked.native.machine.heap value ∧ value.free = [] ∧
        (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1)
        afterCaller.checked.native.machine.heap ∧
      Reserved bits (advance seed (cost inputs)) (cost rest) ∧
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  induction trace generalizing seed inventory roots memos with
  | nil =>
      exact ⟨inventory, memos, roots, Post.refl initial, querySame, safe, paths, counts,
        flags, realized, genuine, fits, known, reserved, originalProjection⟩
  | @cons incoming bucket remaining beforeCaller middleCaller afterCaller before middle after
      queries middleQueries savedQueries fragment fragments outer waiting head tail ih =>
      have actual : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
          bucket incoming beforeCaller before memos.query =
            ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
        simpa only [querySame] using head
      obtain ⟨middleInventory, middleMemos, middleRoots, headPost, headQueries, middleSafe,
        middlePaths, middleCounts, middleFlags, middleRealized, tailGenuine, middleFits,
        middleKnown, tailReservation, middleProjection⟩ :=
        observed_singleton_resources_projection_heap seed formulas solver inventory beforeCaller before
          checkEmpty incoming bucket (remaining ++ rest) roots memos initial safe paths counts flags
          realized genuine fits reserved known originalProjection actual
      obtain ⟨next, final, afterRoots, tailPost, finalQueries, afterSafe, afterPaths, afterCounts,
        afterFlags, afterRealized, afterGenuine, afterFits, afterKnown, afterReserved, afterProjection⟩ :=
        ih (seed := advance seed (bucket.length + 1)) (inventory := middleInventory)
          (roots := middleRoots) (memos := middleMemos) headQueries headPost.context middleSafe
          middlePaths middleCounts middleFlags middleRealized tailGenuine middleFits tailReservation
          middleKnown middleProjection
      refine ⟨next, final, afterRoots, headPost.trans tailPost, finalQueries, afterSafe,
        afterPaths, afterCounts, afterFlags, afterRealized, afterGenuine, ?_, ?_, ?_, afterProjection⟩
      · simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using afterFits
      · simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using afterKnown
      · simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using afterReserved

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
