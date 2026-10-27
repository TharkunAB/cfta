import MicroCFTA.SourcePruningEnumerationIncomingQueryResources
import MicroCFTA.SourcePruningEnumerationSharedTargetArity
import MicroCFTA.SourcePruningEnumerationConjunctionArity

/-!
# Whole edge-record arity at the actual incoming query endpoint

The original resource producer supplies the same complete native receipt.
Its rich native trace preserves arity at the returned intersection heap.
The optional Empty worker uses its actual conjunction call and endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room step)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "workerFuel" => SourceCurrentConjunctionWorklistResources.workerFuel
local notation "readerFuel" => SourceCurrentConjunctionWorklistResources.readerFuel
variable {bits : Nat}

/-- Retain the entire original resource packet and check arity at its same returned native heap. -/
theorem complete_resources_arity
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
    (arity : SourcePruningEnumerationArityOrigins.Heap beforeCaller.checked.native.machine.heap) :
    ∃ (next : Inventory) (query : Node) (queried : Checked (bits + 2))
      (answer : Bool) (checkedAfter : Checked (bits + 2)) (saved : Fourth)
      (final : Memos) (queries : Queries) (replacement : Node) (handle fuel p h : Nat),
      next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        beforeCaller.checked query queried memos ∧
      (∀ extra, SourceEqualityNativeDemand.execute (fuel + extra)
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked = .done query queried) ∧
      (∀ P H, p ≤ P → h ≤ H →
        (if checkEmpty then
          SourcePruningEnumerationEnabledEmpty.check P H query queried beforeCaller.fourth memos.query
        else (.done false queried beforeCaller.fourth, memos.query)) =
          (.done answer checkedAfter saved, queries)) ∧
      Post formulas solver next beforeCaller
        (SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge) final ∧
      final.query = queries ∧ Cache.Extends memos.unfolding final.unfolding ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      replacement = (if answer then .empty else query) ∧
      Available checkedAfter.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode checkedAfter.native.machine.heap handle = some replacement ∧
      (∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) ∧
      (checkEmpty = false → answer = false ∧ replacement = query ∧ checkedAfter = queried ∧
        saved = beforeCaller.fourth ∧ queries = memos.query ∧ final = memos) ∧
      (checkEmpty = true → ∃ reached,
        SourceEndpointMemo.run query memos.query = (reached, queries) ∧
        SourceEndpointMemoCorrect.Checked queried.native.machine.heap memos.query
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained query) (reached, queries) ∧
        (reached = false → answer = false ∧ checkedAfter = queried ∧ saved = beforeCaller.fourth ∧
          final = {memos with query := queries}) ∧
        (reached = true →
          ∃ reachedPhysical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula,
            checkedAfter = advancePhysical queried reachedPhysical ∧
            ∃ actual : SourceCurrentConjunctionMemo.Call 1000 beforeCaller.fourth query
                (physical queried) answer reachedPhysical saved,
              SourceCurrentConjunctionGlobalMemos.CallReads actual {memos with query := queries} final)) ∧
      Fits (step profile) queried ∧ Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) checkedAfter.native.machine.heap ∧
      fuel = instructionBound profile.nodes profile.edges profile.mass + 1 ∧
      p = workerFuel (queryAlphabet alphabet profile) 1000 (scalar (step profile)) ∧
      h = readerFuel (queryAlphabet alphabet profile) 1000 (scalar (step profile)) ∧
      SourcePruningEnumerationArityOrigins.Heap checkedAfter.native.machine.heap := by
  obtain ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
    fuel, p, h, source, roots, receipt, native, phase, post, querySame, unfolding, sound,
    replacementEq, available, closed, encoded, decoded, meaning, disabled, enabled,
    queryFits, finalFits, finalKnown, fuelEq, pEq, hEq⟩ :=
    complete_resources alphabet profile formulas solver inventory beforeCaller left right checkEmpty memos
      initial leftAvailable rightAvailable leftClosed rightClosed fits room known
  have queryArity := receipt.arity_heap initial.ready.good arity
  have finalArity : SourcePruningEnumerationArityOrigins.Heap checkedAfter.native.machine.heap := by
    cases checkEmpty with
    | false =>
        have same := (disabled rfl).2.2.1
        rw [same]
        exact queryArity
    | true =>
        obtain ⟨reached, _guardRun, _guardChecked, skipped, performed⟩ := enabled rfl
        cases reached with
        | false =>
            have same := (skipped rfl).2.1
            rw [same]
            exact queryArity
        | true =>
            obtain ⟨reachedPhysical, same, actual, _reads⟩ := performed rfl
            have ready := SourceCurrentAllocatedConjunctionMemo.ready queried receipt.ready.good
              receipt.ready.semantic receipt.ready.costs
            have current := SourcePruningEnumerationConjunctionArity.call_heap actual ready receipt.available queryArity
            simpa only [same, advancePhysical, SourceRecursiveIntersectionThunks.advance] using current
  exact ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle,
    fuel, p, h, source, roots, receipt, native, phase, post, querySame, unfolding, sound,
    replacementEq, available, closed, encoded, decoded, meaning, disabled, enabled,
    queryFits, finalFits, finalKnown, fuelEq, pEq, hEq, finalArity⟩

end MicroCFTA.SourcePruningEnumerationIncomingQuery
