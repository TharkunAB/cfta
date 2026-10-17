import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryQuery
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold

/-!
# Cold joint checked execution in its concrete input model

The original closed operands determine the model. Initial numeric resources
construct finite execution. The same receipt retains exact language, cap,
occurrence bounds, and causal request origins for later generated queries.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceEqualityNativeDemand SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial counters and source invariants produce every joint and semantic fact needed by the next query. -/
theorem cold_complete (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory machine.heap good.native.machine.1
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
    ∃ fuel value after,
      SourceCurrentConstrainedCapCheckedJointInventoryQuery.Receipt inventory depth formulas solver fuel left right
        ⟨initial (bits + 2) machine, operations⟩ value after := by
  let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory machine.heap good.native.machine.1
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  obtain ⟨fuel, value, after, receipt, _current⟩ := SourceCurrentAllocatedNativeInventoryCold.cold_complete
    bits formulas solver machine operations good semantic left right leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  have context : Context Plain inventory.source machine :=
    ⟨good.native.machine, semantic.ready.semantic, guards, grows_refl _, extends_refl _⟩
  have leftValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
    (SourceEqualityPCSGuard.holds formulas solver) inventory.roots inventory.originals inventory.available inventory.closed
    left (by simp [inventory, SourceCurrentAllocatedNativeInventoryCold.pairInventory])
  have rightValid := SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
    (SourceEqualityPCSGuard.holds formulas solver) inventory.roots inventory.originals inventory.available inventory.closed
    right (by simp [inventory, SourceCurrentAllocatedNativeInventoryCold.pairInventory])
  exact ⟨fuel, value, after, SourceCurrentConstrainedCapCheckedJointInventoryQuery.of_receipt inventory depth
    formulas solver before good semantic rfl context
    (SourceCurrentConstrainedCapCheckedJointCache.initial_stored Plain inventory.source (bits + 2) machine)
    (SourceCurrentConstrainedCapCheckedJointOrigins.initial_stored inventory.source (bits + 2) machine)
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid
    leftCap rightCap fuel value after receipt⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold
