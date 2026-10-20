import MicroCFTA.SourceCurrentAllocatedMergeWorker
import MicroCFTA.SourceCurrentMemoMergeEffects

/-!
# Physical Merge storage does not imply source support

A singleton completed table can return any available closed value from Empty.
The actual warm call retains its full allocated state and its table.
This table need not occur in an execution from an empty completed table.
-/
namespace MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Allocated" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Physical storage permits an unsupported warm result without executing its body. -/
theorem empty_hit (owner : Node) (state : Allocated)
    (available : Available state.heap owner) (closed : owner.free = [])
    (clear : Guard → Bool) (remaining selectionFuel : Nat) :
    ∃ memo : Memo,
      (∀ key, memo key = if key = (Value.empty : Node).referenceOf
        then some ⟨.empty, owner⟩ else none) ∧
      SourceCurrentMemoMergeEffects.Stored state.heap memo ∧
      SourceCurrentAllocatedMergeWorker.call clear (remaining + 1) selectionFuel .empty state memo =
        .done owner state memo ∧
      nodeEdges (Value.empty : Node) = [] := by
  let memo : Memo := fun key => if key = (Value.empty : Node).referenceOf
    then some ⟨.empty, owner⟩ else none
  have stored : SourceCurrentMemoMergeEffects.Stored state.heap memo := by
    intro key entry found
    by_cases same : key = (Value.empty : Node).referenceOf
    · have selected : entry = ⟨.empty, owner⟩ := by
        simpa only [memo, same, ite_eq_left rfl, Option.some.injEq] using found.symm
      subst entry
      exact ⟨same.symm, empty_available state.heap, available, fun _ => closed⟩
    · simp only [memo, ite_eq_right same] at found
      cases found
  refine ⟨memo, fun _ => rfl, stored, ?_, rfl⟩
  exact SourceCurrentAllocatedMergeWorker.call_hit clear remaining selectionFuel .empty state memo
    ⟨.empty, owner⟩ (by simp only [memo, ite_eq_left rfl])

end MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary.empty_hit
#print MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary.empty_hit
#print axioms MicroCFTA.SourceCurrentPhysicalMergeSupportBoundary.empty_hit
