import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
import MicroCFTA.SourceEqualityRequiredSemanticCache
namespace FiniteOrdinaryNarrowKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedFiniteOrdinaryNarrow
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open InternedNestedProvenance (Values)
variable {Symbol Guard : Type}

/-- Two positional changes and final source propagation retain the original forest bounds. -/
theorem serial_propagation {values middle results : List (Value Symbol Guard)}
    (first : All₂ NodeNarrow values middle) (last : All₂ NodeNarrow middle results) :
    All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate results) ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Children (EqualityLeafProjectionRuntimeEmpty.propagate results) ∧
      MergedOrdinaryHeight.childrenHeight (EqualityLeafProjectionRuntimeEmpty.propagate results) ≤ MergedOrdinaryHeight.childrenHeight values ∧
      (EqualityLeafProjectionRuntimeEmpty.propagate results).length = values.length := by
  have related := forest_trans (forest_trans first last) (forest_propagate (forest_domain last))
  exact ⟨related, forest_domain related, forest_height related, related.length_eq.symm⟩

/-- Actual raw row and node reconstruction retain the bound from the full original ordinary parent. -/
theorem raw_constructors [DecidableEq (EdgeKey Symbol Guard)] (edge : EdgeValue Symbol Guard)
    (own : Interned InternedBinderProtocol.NodeKey) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (semantic : SemanticReady state)
    (available : Values state values) (related : All₂ NodeNarrow edge.children values) :
    let rebuilt := run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values) state
    let output := run (InternedConstructorTemplates.makeNode [rebuilt.1]) rebuilt.2
    NodeNarrow (.node own [edge] depth free) output.1 := by
  let rebuilt := run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values) state
  have first := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values state semantic.ready available
  have afterSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values state semantic available
  have bound := SourceCurrentAllocatedFiniteOrdinaryNarrow.makeEdge edge values state
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available related
  exact SourceCurrentAllocatedFiniteOrdinaryNarrow.makeNode own [edge] [rebuilt.1] depth free rebuilt.2
    afterSemantic.ready.semantic.1.normal.facts.coherent afterSemantic.ready.semantic.1.normal.facts.linked
    (by intro row member; cases List.mem_singleton.mp member; exact first.2.1) (.cons bound .nil)

/-- Literal erasure derives output domains and zero height without an input-domain premise. -/
theorem arbitrary_erasure (values : List (Value Symbol Guard)) :
    All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.erase values) ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Children (EqualityLeafProjectionRuntimeEmpty.erase values) ∧
      MergedOrdinaryHeight.childrenHeight (EqualityLeafProjectionRuntimeEmpty.erase values) = 0 := by
  refine ⟨forest_erase values, forest_domain (forest_erase values), ?_⟩
  induction values with
  | nil => rfl
  | cons value values ih => simpa [EqualityLeafProjectionRuntimeEmpty.erase, MergedOrdinaryHeight.childrenHeight,
      MergedOrdinaryHeight.height] using ih
end FiniteOrdinaryNarrowKernels
#print axioms FiniteOrdinaryNarrowKernels.serial_propagation
#check @FiniteOrdinaryNarrowKernels.serial_propagation
#print axioms FiniteOrdinaryNarrowKernels.raw_constructors
#check @FiniteOrdinaryNarrowKernels.raw_constructors
#print axioms FiniteOrdinaryNarrowKernels.arbitrary_erasure
#check @FiniteOrdinaryNarrowKernels.arbitrary_erasure
