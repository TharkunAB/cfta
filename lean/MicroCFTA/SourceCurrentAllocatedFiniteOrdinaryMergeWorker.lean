import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMerge
import MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion

/-!
# Finite ordinary results of literal allocated merge workers

A supplied successful call derives its own current allocated graph.
Initial physical and structural cache facts also construct a finite call.
Larger work and selection bounds retain that exact complete return.
No inventory, language law, or host execution correspondence is asserted.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeWorker
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedMergeGraph.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "Ready" => SourceCurrentConjunctionRowsAllocation.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "StructuralStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "call" => SourceCurrentAllocatedMergeWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A literal successful call retains its own graph, full physical state, memo, and domain result. -/
theorem verified {clear : Guard → Bool} {workFuel selectionFuel : Nat}
    {input output : Value Symbol Guard} {before after : Physical} {memo saved : Memo}
    (done : call clear workFuel selectionFuel input before memo = .done output after saved)
    (ready : Ready before) (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input) :
    SourceCurrentAllocatedMergeGraph.Call clear input before memo output after saved ∧
      Effects before after ∧ PhysicalStored after.heap saved ∧ StructuralStored saved ∧
      Available after.heap output ∧ DNode output := by
  have actual := SourceCurrentAllocatedMergeWorkerSound.call_sound done
  exact ⟨actual, SourceCurrentAllocatedFiniteOrdinaryMerge.allocated actual ready physical structural available domain⟩

/-- Initial cache facts construct literal execution and all larger bounds at the same returned state. -/
theorem finite (clear : Guard → Bool) (input : Value Symbol Guard) (before : Physical) (memo : Memo)
    (ready : Ready before) (physical : PhysicalStored before.heap memo) (structural : StructuralStored memo)
    (available : Available before.heap input) (domain : DNode input) :
    ∃ workFuel selectionFuel output after saved,
      call clear workFuel selectionFuel input before memo = .done output after saved ∧
      (∀ largerWork largerSelection, workFuel ≤ largerWork → selectionFuel ≤ largerSelection →
        call clear largerWork largerSelection input before memo = .done output after saved) ∧
      Effects before after ∧ PhysicalStored after.heap saved ∧ StructuralStored saved ∧
      Available after.heap output ∧ DNode output := by
  obtain ⟨output, after, saved, actual, facts⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMerge.finite clear input before memo ready physical structural available domain
  obtain ⟨workFuel, selectionFuel, stable⟩ := SourceCurrentAllocatedMergeWorkerCompletion.call_complete actual
  exact ⟨workFuel, selectionFuel, output, after, saved,
    stable _ _ (Nat.le_refl _) (Nat.le_refl _), stable, facts⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeWorker
