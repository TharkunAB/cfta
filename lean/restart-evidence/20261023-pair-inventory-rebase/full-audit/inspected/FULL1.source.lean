import MicroCFTA.SourceCurrentAllocatedNativeInventoryRebase
import MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport

namespace MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
local notation "holds" => guardHolds formulas solver
local notation "oldView" => view inventory.source holds
local notation "oldInputs" => inventory.inputs holds

/-- Retain both populated memo families in the computed larger-root inventory. -/
theorem rebase
    (state : Wrapper width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good state.checked)
    (current : At formulas solver inventory state.checked)
    (stable : SourceCurrentSameSymbolEdgeStable.Stable oldView
      (finiteInputMeaning oldView oldInputs) (finiteRankedInput oldView oldInputs) holds state)
    (admitted : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      state.memo.cells handle = some ⟨pair, .returned value⟩ →
      let ordered := if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair
      SourceCurrentAllocatedNativeContextCache.EdgeInputs oldView
        (finiteInputMeaning oldView oldInputs)
        (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain
          (Prod.fst ordered) (Prod.snd ordered)))
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.checked.native.machine.heap left)
    (rightAvailable : Available state.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory
      state.checked.native.machine.heap good.native.machine.1 current.growth current.history
      left right leftAvailable rightAvailable leftClosed rightClosed
    At formulas solver next state.checked ∧
      SourceCurrentSameSymbolEdgeStable.Stable (view next.source holds)
        (finiteInputMeaning (view next.source holds) (next.inputs holds))
        (finiteRankedInput (view next.source holds) (next.inputs holds)) holds state ∧
      (∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
        state.memo.cells handle = some ⟨pair, .returned value⟩ →
        let ordered := if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair
        SourceCurrentAllocatedNativeContextCache.EdgeInputs (view next.source holds)
          (finiteInputMeaning (view next.source holds) (next.inputs holds))
          (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain
            (Prod.fst ordered) (Prod.snd ordered))) ∧
      next.source = state.checked.native.machine.heap ∧
      next.roots = inventory.roots ++ [left, right] ∧
      (next.inputs holds).valid (inputOf left) ∧
      (next.inputs holds).valid (inputOf right) ∧
      SourceCurrentAllocatedNativeContextRebase.Agreement oldInputs (next.inputs holds) := by
  let next : Inventory := SourceCurrentAllocatedNativeInventoryRebase.extend inventory
    state.checked.native.machine.heap good.native.machine.1 current.growth current.history
    left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨nextCurrent, sameSource, sameRoots, leftValid, rightValid⟩ :=
    SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory state.checked
      good current left right leftAvailable rightAvailable leftClosed rightClosed
  have included : ∀ root ∈ inventory.roots, root ∈ next.roots := by
    intro root member
    exact List.mem_append.mpr (Or.inl member)
  have agreement : SourceCurrentAllocatedNativeContextRebase.Agreement oldInputs (next.inputs holds) := by
    exact SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement
      inventory.source state.checked.native.machine.heap inventory.facts good.native.machine.1
      current.growth current.history holds inventory.roots inventory.originals
      inventory.available inventory.closed next.roots next.available next.closed included
  exact ⟨nextCurrent,
    SourceCurrentSameSymbolEdgeModelTransport.rebase oldInputs (next.inputs holds)
      agreement holds state stable admitted,
    (fun handle pair value stored => agreement.edge_inputs (admitted handle pair value stored)),
    sameSource, sameRoots, leftValid, rightValid, agreement⟩

end MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase.rebase
#print MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase.rebase
#print axioms MicroCFTA.SourceCurrentAllocatedNativePairInventoryRebase.rebase
