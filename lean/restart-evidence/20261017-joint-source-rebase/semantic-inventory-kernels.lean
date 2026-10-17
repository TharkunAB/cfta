import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentAllocatedNativeInventoryRebase

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SemanticInventoryIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- The constructed cold result becomes an admitted root at its exact returned heap. -/
theorem produced_result_rebase [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ inventory : Inventory, ∃ fuel value after next,
      inventory.source = machine.heap ∧ inventory.roots = [left, right] ∧
      SourceCurrentAllocatedNativeCoveredQuery.Receipt inventory.source formulas solver
        (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel left right
        ⟨initial (bits + 2) machine, operations⟩ value after ∧
      At formulas solver next after ∧ next.source = after.native.machine.heap ∧
      next.roots = [left, right, value, value] ∧
      (next.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf value) := by
  let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory machine.heap good.native.machine.1
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, receipt, current⟩ :=
    SourceCurrentAllocatedNativeInventoryCold.cold_complete bits formulas solver machine operations good semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory after.native.machine.heap
    receipt.good.native.machine.1 current.growth current.history value value receipt.result receipt.result
    receipt.closed receipt.closed
  have rebased := SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory after receipt.good
    current value value receipt.result receipt.result receipt.closed receipt.closed
  refine ⟨inventory, fuel, value, after, next, rfl, rfl, receipt, rebased.1, rebased.2.1, ?_, rebased.2.2.2.1⟩
  exact rebased.2.2.1

/-- Two model expansions retain the same checked state and the literal root order. -/
theorem two_expansions {width : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (good : Good before)
    (current : At formulas solver inventory before) (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ final : Inventory, At formulas solver final before ∧ final.source = before.native.machine.heap ∧
      final.roots = (inventory.roots ++ [left, right]) ++ [right, left] ∧
      (final.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf right) ∧
      (final.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf left) := by
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap
    good.native.machine.1 current.growth current.history left right leftAvailable rightAvailable leftClosed rightClosed
  have first := SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory before good current
    left right leftAvailable rightAvailable leftClosed rightClosed
  let final := SourceCurrentAllocatedNativeInventoryRebase.extend next before.native.machine.heap
    good.native.machine.1 first.1.growth first.1.history right left rightAvailable leftAvailable rightClosed leftClosed
  have second := SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver next before good first.1
    right left rightAvailable leftAvailable rightClosed leftClosed
  exact ⟨final, second.1, second.2.1, second.2.2.1, second.2.2.2⟩

end MicroCFTA.SemanticInventoryIntegration

#print axioms MicroCFTA.SemanticInventoryIntegration.produced_result_rebase
#check @MicroCFTA.SemanticInventoryIntegration.produced_result_rebase
#print axioms MicroCFTA.SemanticInventoryIntegration.two_expansions
#check @MicroCFTA.SemanticInventoryIntegration.two_expansions
