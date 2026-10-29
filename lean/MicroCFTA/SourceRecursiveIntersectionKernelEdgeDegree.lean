import MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects
import MicroCFTA.SourceRecursiveIntersectionKernel
import MicroCFTA.InternedStoredPlanBinderDepthNormalization
import MicroCFTA.InternedShallowValues

/-!
# Actual mismatched kernel rows have zero returned child degree

The mismatched branch invokes no recursive child.
Canonical readback retains the requested EmptyNode child even on a cache hit.
The actual returned heap retains both source heap invariants.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open InternedConstructorTemplates InternedProbeProvenance
open InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- An actual mismatched row has zero child degree and retains both heap invariants. -/
theorem edge_mismatched_degree
    [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state after : Machine Symbol Guard)
    (value : EdgeValue Symbol Guard)
    (different : left.children.length ≠ right.children.length)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (done : edge emptyGuard conjoin call left right state = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
      manyDepth value.children = 0 := by
  let values : List (Value Symbol Guard) := [.empty]
  let actual := InternedConstructorTemplates.run (makeEdge left.entry.key.symbol emptyGuard values) state.heap
  have inputs : ∀ child ∈ values, Available state.heap child := by
    intro child member
    have same : child = .empty := List.mem_singleton.mp member
    subst child
    exact empty_available _
  have actualDone : (Result.done actual.1 {state with heap := actual.2} : Result Symbol Guard (EdgeValue Symbol Guard)) =
      .done value after := by
    simpa only [edge, ite_eq_right different, work] using done
  obtain ⟨sameValue, sameState⟩ := Result.done.inj actualDone
  rw [← sameState, ← sameValue]
  change SemanticHeap actual.2 ∧ InternedOpenDepthReadback.Heap actual.2 ∧ manyDepth actual.1.children = 0
  refine ⟨SourceRecursiveIntersectionSemanticHeap.edge left.entry.key.symbol emptyGuard values state.heap semantic inputs,
    SourceRecursiveIntersectionOpenDepthEffects.edge left.entry.key.symbol emptyGuard values state.heap opened, ?_⟩
  change manyDepth (InternedConstructorTemplates.run (makeEdge left.entry.key.symbol emptyGuard values) state.heap).1.children = 0
  rw [InternedShallowValues.makeEdge_children left.entry.key.symbol emptyGuard values state.heap
    semantic.1.normal.facts.coherent semantic.1.normal.facts.cached inputs]
  simp [values, manyDepth, valueDepth]

end MicroCFTA.SourceRecursiveIntersectionKernel
