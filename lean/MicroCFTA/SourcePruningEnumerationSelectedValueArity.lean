import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourcePruningEnumerationProbeExposureArity

/-!
# Arity through every actual selected-value endpoint

Stored unfolding retains each copied edge key and its child count.
Union exposure retains the actual endpoint heap.
The final row node does not change the edge-record table.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type} [DecidableEq (EdgeKey Symbol Constraint)]

/-- Every actual selected-value result retains the original edge-record arity invariant. -/
theorem run_heap (fuel : Nat) (value : Value Symbol Constraint) (before : State Symbol Constraint)
    (facts : InternedNestedFacts.Facts before) (heap : Heap before) (available : Available before value) :
    Heap (run fuel value before).state := by
  cases value with
  | empty | reference | node => exact heap
  | mu entry body depth ordinary =>
      have retained := SourcePruningEnumerationArityOrigins.unfold_heap
        (.mu entry body depth ordinary) before facts heap available
      cases observed : InternedFreshOrdinaryStoredSubstitution.unfold
          (.mu entry body depth ordinary) before with
      | done result after | pending key after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            InternedNestedConstruction.Outcome.state] using retained
  | union entry members depth free =>
      have retained := SourcePruningEnumerationProbeExposureArity.nodeEdges_heap fuel
        (.union entry members depth free) before facts heap available
      cases observed : MergedFreshOrdinaryExposure.nodeEdges fuel
          (.union entry members depth free) before with
      | done rows middle =>
          have middleHeap : Heap middle := by
            simpa only [observed, MergedSourceExposure.Result.state] using retained
          simpa only [run, observed, MergedSourceComparison.Result.state] using
            SourcePruningEnumerationArityOrigins.node_heap rows middle middleHeap
      | unresolved name after | pending key after | exhausted after =>
          simpa only [run, observed, MergedSourceComparison.Result.state,
            MergedSourceExposure.Result.state] using retained

end MicroCFTA.SourcePruningEnumerationSelectedValue
