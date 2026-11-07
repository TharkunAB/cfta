import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.MergedFreshOrdinaryConstraintHeap

/-!
# Constraint preservation through selected-value preparation

Every preparation outcome retains the constraint predicate in its actual
returned heap. This includes failed exposure and pending unfolding.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedConstraintHeap
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryConstraintHeap (Heap)

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Preparation preserves the constraint predicate for every fuel and outcome. -/
theorem run_heap (property : Guard → Prop) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (heap : Heap property before) :
    Heap property (SourcePruningEnumerationSelectedValue.run fuel value before).state := by
  cases value with
  | empty | reference | node => exact heap
  | mu entry body depth ordinary =>
      have retained := InternedFreshOrdinaryStoredConstraintHeap.unfold_heap property
        (.mu entry body depth ordinary) before semantic.ready.semantic.1.normal.facts heap available
      cases observed : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before <;>
        simpa only [SourcePruningEnumerationSelectedValue.run, observed,
          InternedNestedConstruction.Outcome.state, MergedSourceComparison.Result.state] using retained
  | union entry members depth free =>
      have retained := MergedFreshOrdinaryConstraintHeap.nodeEdges_heap property fuel
        (.union entry members depth free) before semantic.ready.semantic semantic.ready.covered
        heap available closed
      cases observed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done edges middle =>
          have middleHeap : Heap property middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retained
          simpa only [SourcePruningEnumerationSelectedValue.run, observed,
            MergedSourceComparison.Result.state] using
            InternedFreshOrdinaryConstraintHeap.node_heap property edges middle middleHeap
      | unresolved | pending | exhausted =>
          simpa only [SourcePruningEnumerationSelectedValue.run, observed,
            MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using retained

/-- A completed preparation retains the same predicate in its returned heap. -/
theorem run_done_heap (property : Guard → Prop) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (heap : Heap property before) (result : Value Symbol Guard) (after : State Symbol Guard)
    (completed : SourcePruningEnumerationSelectedValue.run fuel value before = .done result after) :
    Heap property after := by
  simpa only [completed, MergedSourceComparison.Result.state] using
    run_heap property fuel value before semantic available closed heap

end MicroCFTA.SourcePruningEnumerationSelectedConstraintHeap
