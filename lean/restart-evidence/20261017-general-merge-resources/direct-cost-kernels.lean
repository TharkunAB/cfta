import MicroCFTA.SourceCurrentMemoMergeDirectCost
import MicroCFTA.SourceCurrentMemoMergeCompletion
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.DirectCostIntegration
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeDirectCost
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
private def branch (symbol : Nat) : InternedNestedConstruction.Syntax Nat Bool := .node [.mk symbol true []]
private def smallPlan : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 0 true [branch 1], .mk 0 false [branch 2]]
private def largePlan : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 0 true [branch 1], .mk 0 true [branch 2], .mk 0 true [branch 3],
    .mk 0 true [branch 4], .mk 0 true [branch 5]]
private def built (plan : InternedNestedConstruction.Syntax Nat Bool) :=
  InternedFreshOrdinaryConstruction.build plan [] InternedConstructorTemplates.empty
private def source (plan : InternedNestedConstruction.Syntax Nat Bool) : Value Nat Bool :=
  match built plan with | .done value _ => value | .pending .. => .empty
private def heap (plan : InternedNestedConstruction.Syntax Nat Bool) := (built plan).state
private def rows (plan : InternedNestedConstruction.Syntax Nat Bool) := InternedEdgeResidency.nodeEdges (source plan)
private def columnInputs : List (Value Nat Bool) := (rows largePlan).map (fun row => row.children.getD 0 .empty)

private theorem constructed (plan : InternedNestedConstruction.Syntax Nat Bool) :
    built plan = .done (source plan) (heap plan) := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, source, heap, done, InternedNestedConstruction.Outcome.state]

private theorem source_facts (plan : InternedNestedConstruction.Syntax Nat Bool) :
    SemanticReady (heap plan) ∧ CostHeap (heap plan) ∧ Available (heap plan) (source plan) := by
  have done := constructed plan
  have available := (InternedFreshOrdinaryFacts.closed_verified plan).result (source plan) (heap plan) done
  have semantic := SourceEqualityRequiredSemanticCache.constructed plan (source plan) (heap plan) done
  have costs : CostHeap (heap plan) := InternedFreshOrdinaryCosts.closed_heap plan
  exact ⟨semantic, costs, available⟩

private theorem completed (plan : InternedNestedConstruction.Syntax Nat Bool) :
    ∃ result after saved events cost,
      Run id true (body true (source plan)) (heap plan) empty result after saved ∧
      Counted id true (body true (source plan)) (heap plan) empty result after saved events cost ∧
      cost ≤ bodyBudget (InternedValueMass.value (source plan)) ∧
      (∀ event ∈ events, SourceCurrentMemoMergeRequestBounds.Reached
        (MergedOrdinaryHeight.height (source plan)) (heap plan) event) ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧ Available after result := by
  obtain ⟨semantic, costs, available⟩ := source_facts plan
  obtain ⟨result, after, saved, actual, effect, stored, returned, _⟩ :=
    SourceCurrentMemoMergeCompletion.body_complete id true (source plan) (heap plan) empty semantic costs
      (SourceCurrentMemoMergeEffects.stored_empty _) available
  obtain ⟨events, cost, counted, bounded, requests⟩ := body_bound actual semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty _) available _ (Nat.le_refl _)
  exact ⟨result, after, saved, events, cost, actual, counted, bounded, requests, stored, returned⟩

/-- Two literal source rows construct their own completed small-group body and direct count. -/
theorem actual_small_group :
    built smallPlan = .done (source smallPlan) (heap smallPlan) ∧
    (MergedSourceGrouping.groups (rows smallPlan)).map List.length = [2] ∧
    ∃ result after saved events cost,
      Run id true (body true (source smallPlan)) (heap smallPlan) empty result after saved ∧
      Counted id true (body true (source smallPlan)) (heap smallPlan) empty result after saved events cost ∧
      cost ≤ bodyBudget (InternedValueMass.value (source smallPlan)) ∧
      (∀ event ∈ events, SourceCurrentMemoMergeRequestBounds.Reached
        (MergedOrdinaryHeight.height (source smallPlan)) (heap smallPlan) event) ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧ Available after result :=
  ⟨constructed smallPlan, by cbv, completed smallPlan⟩

/-- Five distinct source rows construct their own completed large-group body and direct count. -/
theorem actual_large_group :
    built largePlan = .done (source largePlan) (heap largePlan) ∧
    (MergedSourceGrouping.groups (rows largePlan)).map List.length = [5] ∧
    columnInputs.length = 5 ∧ columnInputs.any MergedOrdinaryHeight.recursiveBoundary = false ∧
    ∃ result after saved events cost,
      Run id true (body true (source largePlan)) (heap largePlan) empty result after saved ∧
      Counted id true (body true (source largePlan)) (heap largePlan) empty result after saved events cost ∧
      cost ≤ bodyBudget (InternedValueMass.value (source largePlan)) ∧
      (∀ event ∈ events, SourceCurrentMemoMergeRequestBounds.Reached
        (MergedOrdinaryHeight.height (source largePlan)) (heap largePlan) event) ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧ Available after result :=
  ⟨constructed largePlan, by cbv, by cbv, by cbv, completed largePlan⟩

/-- The actual large column selects five ordinary children, builds their union, and makes one opaque request. -/
theorem actual_retained_union_request :
    ∃ joined result after saved,
      run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan) = joined ∧
      SourceMergedSelection.select id 0 columnInputs (heap largePlan) = .done columnInputs (heap largePlan) ∧
      Call id true joined.1 joined.2 empty result after saved ∧
      Counted id true (column columnInputs) (heap largePlan) empty result after saved
        [⟨joined.1, joined.2, empty, result, after, saved⟩] 5 ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧ Available after result ∧
      Call id true joined.1 after saved result after saved := by
  obtain ⟨semantic, costs, available⟩ := source_facts largePlan
  have sameChildren : columnInputs = children (source largePlan) := by cbv
  have inputs : InternedNestedProvenance.Values (heap largePlan) columnInputs := by
    rw [sameChildren]
    exact available.children
  have closed : MergedColdReaderClosedInputs.ClosedValues columnInputs := by
    have frees : columnInputs.map Value.free = [[], [], [], [], []] := by cbv
    intro value member
    have included : value.free ∈ columnInputs.map Value.free := List.mem_map.mpr ⟨value, member, rfl⟩
    rw [frees] at included
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using included
  have selected : SourceMergedSelection.select id 0 columnInputs (heap largePlan) =
      .done columnInputs (heap largePlan) := by cbv
  have physicalRows := SourceMergedCache.ordinary_rows columnInputs (heap largePlan) semantic inputs closed
  have node := SourceEqualityRequiredCache.node _ (heap largePlan) semantic.ready physicalRows.1 physicalRows.2
  have nextSemantic := SourceEqualityRequiredSemanticCache.node _ (heap largePlan) semantic physicalRows.1 physicalRows.2
  have nextCosts : CostHeap (run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).2 :=
    InternedFreshOrdinaryCostHeap.preserve _ _ costs (InternedShallowHeap.makeNode_noNewMu _ _)
  obtain ⟨result, after, saved, actual, effect, stored, returned, _⟩ :=
    SourceCurrentMemoMergeCompletion.cold_complete id true _ _ nextSemantic nextCosts node.2.1
  have branch : retainedColumn columnInputs =
      .bind (.work (MergedOrdinaryHeight.ordinaryUnion columnInputs)) Code.request := by cbv
  have counted : Counted id true (column columnInputs) (heap largePlan) empty result after saved
      [⟨(run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).1,
         (run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).2,
         empty, result, after, saved⟩] 5 := by
    have retained : Counted id true (retainedColumn columnInputs)
        (heap largePlan) empty result after saved
        [⟨(run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).1,
           (run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).2,
           empty, result, after, saved⟩] 3 := by
      rw [branch]
      exact .bind (.work _ _ _) (.request actual)
    exact .bind (.select 0 selected) retained
  obtain ⟨entry, found, same⟩ := actual.present
  have warm : Call id true (run (MergedOrdinaryHeight.ordinaryUnion columnInputs) (heap largePlan)).1
      after saved result after saved := by
    rw [same]
    exact .hit found
  exact ⟨_, result, after, saved, rfl, selected, actual, counted, stored, returned, warm⟩

#print axioms actual_small_group
#check @actual_small_group
#print axioms actual_large_group
#check @actual_large_group
#print axioms actual_retained_union_request
#check @actual_retained_union_request
end MicroCFTA.DirectCostIntegration
