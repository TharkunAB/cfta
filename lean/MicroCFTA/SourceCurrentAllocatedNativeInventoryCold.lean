import MicroCFTA.SourceCurrentAllocatedNativeInventoryState
import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges

/-!
# Cold checked queries in a concrete input inventory

The two closed operands determine the finite input model before execution.
Initial counters derive all reached word checks. The returned receipt retains
this same model and admission for every actual native memo cell.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- The literal operand pair supplies one concrete closed original input inventory. -/
def pairInventory (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) : Inventory where
  source := source
  facts := facts
  roots := [left, right]
  originals := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftOriginal
    · exact rightOriginal
  available := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftAvailable
    · exact rightAvailable
  closed := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact leftClosed
    · exact rightClosed

/-- Initial numeric resources construct a full checked receipt in the computed pair model. -/
theorem cold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    let inventory := pairInventory machine.heap good.native.machine.1 left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
    ∃ fuel value after,
      SourceCurrentAllocatedNativeCoveredQuery.Receipt inventory.source formulas solver
        (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel left right
        ⟨initial (bits + 2) machine, operations⟩ value after ∧
      At formulas solver inventory after := by
  let inventory := pairInventory machine.heap good.native.machine.1 left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  have current := SourceCurrentAllocatedNativeInventoryState.initial inventory formulas solver (bits + 2)
    machine operations (grows_refl _) (extends_refl _)
  have ranges := (SourceCurrentAllocatedRecursiveInitialRanges.initial_ranges bits machine operations good semantic
    left right leftOriginal rightOriginal leftAvailable rightAvailable nodes edges room).1
  have leftValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
    (SourceEqualityPCSGuard.holds formulas solver) inventory.roots inventory.originals inventory.available
    inventory.closed left (by simp [inventory, pairInventory])
  have rightValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
    (SourceEqualityPCSGuard.holds formulas solver) inventory.roots inventory.originals inventory.available
    inventory.closed right (by simp [inventory, pairInventory])
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeCoveredQuery.query_complete
    inventory.source inventory.facts formulas solver (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver))
    before good current.contextual current.covered
    (SourceCurrentAllocatedNativeScopeCache.initial_scoped (bits + 2) machine) semantic
    (SourceRecursiveIntersectionNative.idle_initial machine) (grows_refl _) (extends_refl _)
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid ranges
  exact ⟨fuel, value, after, receipt, receipt.contextual, receipt.covered, receipt.extension.heap, receipt.extension.history⟩

end MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
