import MicroCFTA.SourceCurrentConstrainedCapEditReceipt

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.EditReceiptIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

/-- An actual unselected child scan derives its receipt without a callback or completed-read premise. -/
theorem unselected_child (frame : Frame formulas solver inventory before.checked)
    (ready : Ready formulas solver inventory record originals base before)
    (value : Value Symbol Guard) (available : Available before.checked.native.machine.heap value)
    (memos : EndpointMemoGateTrace.Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ actual : EditChildren record originals [] 0 [value] before [value] before,
      ChildrenReads formulas solver base actual memos memos ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver inventory record originals base
          [value] before [value] before memos memos := by
  let actual : EditChildren record originals [] 0 [value] before [value] before :=
    .unselected 0 rfl .nil
  have reads : ChildrenReads formulas solver base actual memos memos := .unselected (absent := rfl) .nil
  have receipt := SourceCurrentConstrainedCapEditReceipt.children reads
    (by simp [Populated])
    (by simp [Allowed, SourceEqualityEdits.All]) ready
    (fun child member => (List.mem_singleton.mp member) ▸ available)
    (by intro query child found; cases found) valid frame
  exact ⟨actual, reads, receipt⟩

/-- A literal raw-row rebuild derives its returned frame and full receipt from the same constructor request. -/
theorem rebuild_empty_row (profile : Profile) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored record originals before) (entry : Interned (EdgeKey Symbol Guard))
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap (.mk entry []))
    (memos : EndpointMemoGateTrace.Memos) (valid : Valid before.checked.native.machine.heap memos) :
    let work := run (makeEdge entry.key.symbol entry.key.constraint []) before.checked.native.machine.heap
    let after := advanceHeap before work.2
    ∃ actual : EditRows record originals [] [.mk entry []] before [work.1] after,
      RowsReads formulas solver base actual memos memos ∧
        SourceCurrentAllocatedSharedEditEffects.RowsReceipt formulas solver inventory record originals base
          [.mk entry []] before [work.1] after memos memos ∧
        Frame formulas solver inventory after.checked ∧
        Fits (SourceCurrentConstrainedCapEditFrame.constructorProfile 0 profile) after.checked ∧
        Stored record originals after ∧ [work.1].length = [EdgeValue.mk entry []].length := by
  let work := run (makeEdge entry.key.symbol entry.key.constraint []) before.checked.native.machine.heap
  let after := advanceHeap before work.2
  let actual : EditRows record originals [] [.mk entry []] before [work.1] after := .cons .nil rfl .nil
  have reads : RowsReads formulas solver base actual memos memos := .cons .nil .nil
  have field := ready.checked.good.fields _ _ resident
  have returned := SourceCurrentConstrainedCapEditFrame.edge profile 0 frame fits ready
    entry.key.symbol entry.key.constraint [] field (by intro value member; cases member)
    (Nat.le_refl _) stored
  have receipt := SourceCurrentConstrainedCapEditReceipt.rows reads
    (by simp [Populated])
    (by simp [Allowed, SourceEqualityEdits.All]) ready
    (fun edge member => (List.mem_singleton.mp member) ▸ resident)
    (by intro edge member query child found; cases found) valid returned.1
  exact ⟨actual, reads, receipt, returned.1, returned.2.1, returned.2.2.1,
    SourceCurrentConstrainedCapEditReceipt.rows_length actual⟩

end MicroCFTA.EditReceiptIntegration

#print axioms MicroCFTA.EditReceiptIntegration.unselected_child
#check @MicroCFTA.EditReceiptIntegration.unselected_child
#print axioms MicroCFTA.EditReceiptIntegration.rebuild_empty_row
#check @MicroCFTA.EditReceiptIntegration.rebuild_empty_row
