import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourceCurrentAllocatedProbeExposure
import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.InternedFreshOrdinaryStoredCosts

/-!
# Native physical invariants through one selected-value operation

Actual stored unfolding retains costs, filtered probes and edge annotations.
Union row exposure retains those invariants at every bounded outcome.
The final node constructor adds no Mu and copies the existing annotations.
The caller can keep its equality-operation state unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "Fields" => SourceEqualityAnnotationHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual selected-value outcome retains the three original physical heap invariants. -/
theorem run_heaps (property : Guard → Prop) (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (costs : CostHeap before) (probes : ProbeHeap before) (fields : Fields property before) :
    CostHeap (run fuel value before).state ∧ ProbeHeap (run fuel value before).state ∧
      Fields property (run fuel value before).state := by
  cases value with
  | empty | reference | node => exact ⟨costs, probes, fields⟩
  | mu entry body depth ordinary =>
      have retainedCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
        (.mu entry body depth ordinary) before semantic.ready.semantic.1
        semantic.ready.semantic.2 costs available
      have retainedProbes := SourceEqualityProbeUnfold.unfold
        (.mu entry body depth ordinary) before semantic.ready.semantic.1 probes available
      have retainedFields : Fields property
          (InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before).state := by
        simpa only [InternedFreshOrdinaryConstraintHeap.Heap, SourceEqualityAnnotationHeap.Heap] using
          InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property
            (.mu entry body depth ordinary) before semantic.ready.semantic.1.normal.facts fields available
      cases observed : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done result after | pending key after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            InternedNestedConstruction.Outcome.state] using
            And.intro retainedCosts (And.intro retainedProbes retainedFields)
  | union entry members depth free =>
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel
        (.union entry members depth free) before semantic costs available
      have retainedProbes := SourceCurrentAllocatedProbeExposure.nodeEdges_heap fuel
        (.union entry members depth free) before semantic probes available
      have retainedFields := SourceCurrentOpenExposureFields.nodeEdges_heap property fuel
        (.union entry members depth free) before semantic fields available
      cases observed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have middleCosts : CostHeap middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using checked.costs
          have middleProbes : ProbeHeap middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retainedProbes
          have middleFields : Fields property middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retainedFields
          have finalCosts := InternedFreshOrdinaryCostHeap.preserve middle _ middleCosts
            (InternedShallowHeap.makeNode_noNewMu rows middle)
          have finalProbes := InternedFreshOrdinaryProbeHeap.node rows middle middleProbes
          have finalFields := SourceEqualityAnnotationHeap.run property _
            (SourceEqualityAnnotationHeap.makeNode property rows) middle middleFields
          simpa only [run, observed, MergedSourceComparison.Result.state] using
            And.intro finalCosts (And.intro finalProbes finalFields)
      | unresolved name after | pending key after | exhausted after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            MergedSourceExposure.Result.state] using
            And.intro checked.costs (And.intro retainedProbes retainedFields)

/-- A completed actual worker supplies the same invariants at its complete returned native heap. -/
theorem run_invariants (property : Guard → Prop) (fuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value)
    (costs : CostHeap before) (probes : ProbeHeap before) (fields : Fields property before)
    (observed : run fuel value before = .done result after) :
    CostHeap after ∧ ProbeHeap after ∧ Fields property after := by
  simpa only [observed, MergedSourceComparison.Result.state] using
    run_heaps property fuel value before semantic available costs probes fields

end MicroCFTA.SourcePruningEnumerationSelectedValue
