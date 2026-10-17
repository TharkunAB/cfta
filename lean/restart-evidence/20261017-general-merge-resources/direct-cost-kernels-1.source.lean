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
  have costs : CostHeap (heap plan) := by
    simpa only [done, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap plan
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

#print axioms actual_small_group
#check @actual_small_group
#print axioms actual_large_group
#check @actual_large_group
end MicroCFTA.DirectCostIntegration
