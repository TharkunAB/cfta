import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryCold

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 2000000

namespace MicroCFTA.JointInventoryIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Receipt" => SourceCurrentConstrainedCapCheckedJointInventoryQuery.Receipt
local notation "Cap" => SourceCurrentConstrainedCap.Cap
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A constructed cold result supplies the next actual operand and every nonnumeric entry invariant. -/
theorem cold_result_fed (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : Cap Plain depth left) (rightCap : Cap Plain depth right)
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ (inventory : Inventory) (fuel : Nat) (first : Value Symbol Guard) (middle : Checked (bits + 2)),
      inventory.source = machine.heap ∧ inventory.roots = [left, right] ∧
      Receipt inventory depth formulas solver fuel left right ⟨initial (bits + 2) machine, operations⟩ first middle ∧
      (middle.native.machine.heap.nodes.next < 2 ^ bits →
       middle.native.machine.heap.edges.next ≤ 2 ^ (bits + 2) →
       middle.native.machine.domains.next +
         2 ^ (middle.native.machine.heap.nodes.next +
           middle.native.machine.heap.nodes.next * middle.native.machine.heap.nodes.next) < 2 ^ (bits + 1) →
       ∃ (next : Inventory) (count : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
         next.source = middle.native.machine.heap ∧ next.roots = [left, right, first, right] ∧
         Receipt next depth formulas solver count first right middle value after ∧
         At formulas solver next after ∧
         execute (count + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain first right)) middle = .done value after ∧
         Available after.native.machine.heap value ∧ value.free = [] ∧ Cap Plain depth value ∧
         Context Plain next.source after.native.machine ∧ Joint Plain next.source after.native ∧
         Origins next.source after.native ∧
         (∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
           InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
           InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term)) := by
  let inventory := SourceCurrentAllocatedNativeInventoryCold.pairInventory machine.heap good.native.machine.1
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, first, middle, receipt⟩ :=
    SourceCurrentConstrainedCapCheckedJointInventoryCold.cold_complete bits depth formulas solver machine operations
      good semantic guards left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
      leftCap rightCap nodes edges room
  refine ⟨inventory, fuel, first, middle, rfl, rfl, receipt, ?_⟩
  intro nextNodes nextEdges nextRoom
  have current := receipt.inventoryAt
  have grownRight : Available middle.native.machine.heap right :=
    rightAvailable.grows machine.heap middle.native.machine.heap receipt.context.growth receipt.context.history
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory middle.native.machine.heap
    receipt.good.native.machine.1 current.growth current.history first right receipt.result grownRight receipt.closed rightClosed
  obtain ⟨count, value, after, returned⟩ :=
    SourceCurrentConstrainedCapCheckedJointInventoryQuery.generated_complete bits depth formulas solver inventory middle
      receipt.good current receipt.semantic receipt.context receipt.stored receipt.origins receipt.scopedCache receipt.idle
      first right receipt.result grownRight receipt.closed rightClosed receipt.cap rightCap nextNodes nextEdges nextRoom
  refine ⟨next, count, value, after, rfl, rfl, returned, returned.inventoryAt,
    returned.toCoveredReceipt.toWarmReceipt.done, returned.result, returned.closed, returned.cap,
    returned.context, returned.stored, returned.origins, ?_⟩
  intro output term
  rw [returned.meaning, receipt.meaning]
  simp only [and_assoc, and_self]

#print axioms cold_result_fed
#check @cold_result_fed

/-- A literal Mu and a nonhereditary nullary cap construct both queries without a supplied return. -/
theorem mixed_mu_bad_cap_result_fed (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (muEntry nodeEntry : Interned InternedConstructorTemplates.NodeKey) (body depth ordinary : Value Symbol Guard)
    (edge : EdgeValue Symbol Guard) (level : Nat)
    (annotated : SourceEqualityAnnotationLanguage.Annotated Plain body)
    (children : edge.children = []) (outside : ¬ Plain edge.entry.key.constraint)
    (muAvailable : Available machine.heap (.mu muEntry body depth ordinary))
    (nodeAvailable : Available machine.heap (.node nodeEntry [edge] level []))
    (muClosed : (Value.mu muEntry body depth ordinary).free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    let left := Value.mu muEntry body depth ordinary
    let right := Value.node nodeEntry [edge] level []
    ¬ SourceEqualityAnnotationLanguage.Annotated Plain right ∧
    ∃ (inventory : Inventory) (fuel : Nat) (first : Value Symbol Guard) (middle : Checked (bits + 2)),
      Receipt inventory 1 formulas solver fuel left right ⟨initial (bits + 2) machine, operations⟩ first middle ∧
      (middle.native.machine.heap.nodes.next < 2 ^ bits →
       middle.native.machine.heap.edges.next ≤ 2 ^ (bits + 2) →
       middle.native.machine.domains.next +
         2 ^ (middle.native.machine.heap.nodes.next +
           middle.native.machine.heap.nodes.next * middle.native.machine.heap.nodes.next) < 2 ^ (bits + 1) →
       ∃ (next : Inventory) (count : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
         Receipt next 1 formulas solver count first right middle value after ∧
         next.roots = [left, right, first, right] ∧ At formulas solver next after ∧
         execute (count + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain first right)) middle = .done value after ∧
         Cap Plain 1 value ∧ Original value) := by
  let left := Value.mu muEntry body depth ordinary
  let right := Value.node nodeEntry [edge] level []
  have rightCap : Cap Plain 1 right := by
    apply SourceCurrentConstrainedCap.Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have leftCap : Cap Plain 1 left := .plain 1 (.mu muEntry body depth ordinary annotated)
  have leftOriginal : Original left := SourceRecursiveIntersectionOriginalOutput.closed_original left machine.heap
    good.native.machine.1.coherent muAvailable muClosed
  have rightOriginal : Original right := SourceRecursiveIntersectionOriginalOutput.closed_original right machine.heap
    good.native.machine.1.coherent nodeAvailable rfl
  constructor
  · intro supposed
    exact outside (SourceCurrentHereditaryConstructors.node_edge supposed edge List.mem_cons_self).1
  obtain ⟨inventory, fuel, first, middle, _source, _roots, receipt, later⟩ :=
    cold_result_fed bits 1 formulas solver machine operations good semantic guards left right leftOriginal rightOriginal
      muAvailable nodeAvailable muClosed rfl leftCap rightCap nodes edges room
  refine ⟨inventory, fuel, first, middle, receipt, ?_⟩
  intro nextNodes nextEdges nextRoom
  obtain ⟨next, count, value, after, _source, roots, returned, atNext, done, _available, _closed, cap,
      _context, _stored, _origins, _meaning⟩ := later nextNodes nextEdges nextRoom
  exact ⟨next, count, value, after, returned, roots, atNext, done, cap, returned.original⟩

#print axioms mixed_mu_bad_cap_result_fed
#check @mixed_mu_bad_cap_result_fed
end MicroCFTA.JointInventoryIndependent
