import MicroCFTA.SourcePruningEnumerationIncomingObservedResources
import MicroCFTA.SourcePruningEnumerationParentProjectionScan

/-!
# Projection support at actual incoming query returns

The original resource producer supplies the complete native query receipt.
Its actual trace and optional Empty call preserve the original projection heap.
Successful observations identify the same returned checked state and replacement.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {bits : Nat}

/-- Original resources and actual query observations derive the returned heap and child annotation support. -/
theorem raw_done_resources_projection_heap
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (left right : Node) (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (leftAvailable : Available beforeCaller.checked.native.machine.heap left)
    (rightAvailable : Available beforeCaller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {fuel p h : Nat} {query : Node} {queried checkedAfter : Checked (bits + 2)}
    {answer : Bool} {saved : Fourth} {queries : Queries}
    (native : SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done query queried)
    (phase : (if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
      else (.done false queried beforeCaller.fourth, memos.query)) =
        (.done answer checkedAfter saved, queries)) :
    Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
        checkedAfter.native.machine.heap ∧
      ProjectionHeap checkedAfter.native.machine.heap ∧
      SourceEqualityAnnotationLanguage.Annotated projectable (if answer then .empty else query) := by
  obtain ⟨_next, result, reached, producedAnswer, finish, workerSaved, _final, savedQueries,
    replacement, _handle, n, P, H, _source, _roots, receipt, producedNative, producedPhase,
    post, _querySame, _unfolding, _sound, replacementSame, available, _closed, _encoded,
    _decoded, _meaning, disabled, enabled, _queryFits, returnedFits, returnedKnown,
    _fuelSame, _pSame, _hSame⟩ :=
    complete_resources alphabet profile formulas solver inventory beforeCaller left right checkEmpty memos
      initial leftAvailable rightAvailable leftClosed rightClosed fits room known
  have queryProjection := receipt.projection_heap initial.ready.good originalProjection
  have finalProjection : ProjectionHeap finish.native.machine.heap := by
    cases checkEmpty with
    | false =>
        have same := (disabled rfl).2.2.1
        rw [same]
        exact queryProjection
    | true =>
        obtain ⟨accessible, _guardRun, _guardChecked, skipped, performed⟩ := enabled rfl
        cases accessible with
        | false =>
            have same := (skipped rfl).2.1
            rw [same]
            exact queryProjection
        | true =>
            obtain ⟨reachedPhysical, same, actual, _reads⟩ := performed rfl
            have ready := SourceCurrentAllocatedConjunctionMemo.ready reached receipt.ready.good
              receipt.ready.semantic receipt.ready.costs
            have current := SourcePruningEnumerationConjunctionProjectionHeap.call_heap actual ready
              receipt.available queryProjection
            simpa only [same, advancePhysical, SourceRecursiveIntersectionThunks.advance] using current
  have replacementAnnotated : SourceEqualityAnnotationLanguage.Annotated projectable
      (if producedAnswer then .empty else result) := by
    rw [← replacementSame]
    exact SourceEqualityAnnotationHeap.available projectable finish.native.machine.heap finalProjection
      post.context.ready.semantic.ready.semantic.1.normal.facts.linked replacement available
  have produced : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done result reached := by
    simpa only [Nat.add_zero] using producedNative 0
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique fuel n _
    beforeCaller.checked queried reached query result native produced
  obtain ⟨sameAnswer, sameState, _sameMemo, _sameQueries⟩ :=
    SourcePruningEnumerationEnabledEmpty.optional_done_unique checkEmpty phase
      (producedPhase P H (Nat.le_refl _) (Nat.le_refl _))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sameState]
    exact returnedFits
  · rw [sameState]
    exact returnedKnown
  · rw [sameState]
    exact finalProjection
  · rw [sameAnswer]
    exact replacementAnnotated

end MicroCFTA.SourcePruningEnumerationIncomingQuery
