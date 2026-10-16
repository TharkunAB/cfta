import MicroCFTA.SourceCurrentAllocatedMergeWorkerActual

#print axioms MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.verified
#check MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.caller
#check MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.caller
#print axioms MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.finite
#check MicroCFTA.SourceCurrentAllocatedMergeWorkerActual.finite

namespace MicroCFTA.AllocatedMergeActualReview
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

 theorem finite_actual_state_and_bound
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {input : Value Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap input) :
    ∃ output after saved final workBound selectionBound,
      (∀ workFuel selectionFuel, workBound ≤ workFuel → selectionBound ≤ selectionFuel →
        SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear workFuel selectionFuel
          input (physical before.checked) before.merge = .done output after saved) ∧
      let returned := SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked after) before.fourth saved
      Post formulas solver inventory before returned final ∧
      InternedFreshOrdinaryProbeHeap.Heap returned.checked.native.machine.heap ∧
      returned.checked.operations = after.equality ∧ returned.checked.native.nodes = before.checked.native.nodes ∧
      returned.checked.native.edges = before.checked.native.edges ∧
      returned.checked.native.machine.domains = before.checked.native.machine.domains ∧
      returned.nodeResults = before.nodeResults ∧ returned.edgeResults = before.edgeResults ∧
      Available after.heap output ∧ (input.free = [] → output.free = []) ∧
      ∀ ambient, SourceCurrentMemoMergeLanguage.Covers (SourceEqualityPCSGuard.holds formulas solver) ambient input output := by
  obtain ⟨output, after, saved, final, work, selection, stable, post, resident, closed, included⟩ :=
    SourceCurrentAllocatedMergeWorkerActual.finite formulas solver initial available
  exact ⟨output, after, saved, final, work, selection, stable, post, post.context.probes,
    rfl, rfl, rfl, rfl, rfl, rfl, resident, closed, included⟩

end MicroCFTA.AllocatedMergeActualReview
