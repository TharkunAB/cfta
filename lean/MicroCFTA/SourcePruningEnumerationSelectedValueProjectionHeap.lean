import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourcePruningEnumerationConstraint
import MicroCFTA.SourceEqualityAnnotationExposure

/-!
# Projectability through actual selected-value preparation

The original physical heap supplies every edge projection.
Stored unfolding copies those guards. Union exposure retains them.
The final row-node constructor adds no edge guard.
The result includes actual failed endpoints without a stability claim.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap projectable
variable {Symbol : Type} [DecidableEq (EdgeKey Symbol Constraint)]

/-- Every actual selected-value endpoint retains the original physical projection heap. -/
theorem run_projectable_heap
    (fuel : Nat) (value : Value Symbol Constraint) (before : State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (heap : Heap before) : Heap (run fuel value before).state := by
  cases value with
  | empty | reference | node => exact heap
  | mu entry body depth ordinary =>
      have retained := SourceEqualityAnnotationUnfold.unfold projectable
        (.mu entry body depth ordinary) before heap ready.semantic.1.normal.facts available
      cases observed : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done result after | pending key after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            InternedNestedConstruction.Outcome.state] using retained
  | union entry members depth free =>
      have retained := SourceEqualityAnnotationExposure.nodeEdges_heap projectable fuel
        (.union entry members depth free) before ready.semantic ready.covered heap available closed
      cases observed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have middleHeap : Heap middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retained
          simpa only [run, observed, MergedSourceComparison.Result.state] using
            SourceEqualityAnnotationHeap.run projectable (makeNode rows)
              (SourceEqualityAnnotationHeap.makeNode projectable rows) middle middleHeap
      | unresolved name after | pending key after | exhausted after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            MergedSourceExposure.Result.state] using retained

end MicroCFTA.SourcePruningEnumerationSelectedValue
