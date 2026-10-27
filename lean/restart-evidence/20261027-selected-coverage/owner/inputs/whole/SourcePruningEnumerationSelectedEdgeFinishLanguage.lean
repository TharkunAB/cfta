import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.EnumerationSemantics

/-!
# Assignment meaning of the actual selected-edge residual write

The final cache stores the complete projected residual on its actual fragment.
The native language, forest, value slots and earlier obligations stay fixed.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedEdge
open Language EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol

/-- The actual final write adds exactly the residual predicate at the filled edge fragment. -/
theorem finish_semantics
    (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) :
    Satisfies language meaning assignment (finish residual fragment before).core ↔
      Satisfies language meaning assignment before.core ∧
      ResidualHolds meaning residual (Fragments.fill assignment fragment) := by
  apply EnumerationSemantics.recordResidual_assignment language meaning assignment residual fragment before.core
    (finish residual fragment before).core
  rw [Success, finish_raw]
  exact List.mem_singleton_self _

end MicroCFTA.SourcePruningEnumerationSelectedEdge
