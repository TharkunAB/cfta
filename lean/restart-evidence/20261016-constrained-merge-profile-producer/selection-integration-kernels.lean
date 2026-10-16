import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeSelection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace

namespace MergeOrdinarySelectionIntegration
open MicroCFTA Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A literal zero-fuel column deduplicates repeated ordinary inputs without constructor work. -/
theorem duplicate_column (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (rows arity : Nat)
    (profile : NodeShape rows arity value) :
    Run clear top (column [value, value]) before memo value before memo ∧ Trace before before [] := by
  have selected := SourceCurrentAllocatedFiniteOrdinaryMergeSelection.select clear 0 [value, value] before
    (show ChildrenShape rows arity [value, value] from ⟨profile, profile, True.intro⟩)
  have distinct : distinctNodes [value, value] = [value] := by simp [distinctNodes]
  rw [distinct] at selected
  refine ⟨.bind (.select 0 selected) ?_, .refl before⟩
  exact .pure value before memo

/-- An actual ordinary selection has an empty constructor trace at the same whole returned heap. -/
theorem actual_selection_trace {clear : Guard → Bool} {fuel : Nat} {inputs values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {rows arity : Nat} (profile : ChildrenShape rows arity inputs)
    (actual : SourceMergedSelection.select clear fuel inputs before = .done values after) :
    values = distinctNodes inputs ∧ Trace before after [] ∧
      after.nodes.next = before.nodes.next ∧ after.edges.next = before.edges.next := by
  have result := SourceCurrentAllocatedFiniteOrdinaryMergeSelection.done profile actual
  rw [result.2]
  exact ⟨result.1, .refl before, rfl, rfl⟩

end MergeOrdinarySelectionIntegration

#print axioms MergeOrdinarySelectionIntegration.duplicate_column
#check @MergeOrdinarySelectionIntegration.duplicate_column
#print axioms MergeOrdinarySelectionIntegration.actual_selection_trace
#check @MergeOrdinarySelectionIntegration.actual_selection_trace
