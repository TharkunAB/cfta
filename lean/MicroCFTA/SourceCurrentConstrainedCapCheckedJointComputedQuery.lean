import MicroCFTA.SourceCurrentConstrainedCapCheckedJointInventoryQuery
import MicroCFTA.SourceCurrentAllocatedNativeComputedBudget

/-!
# Computed resources for generated joint checked queries

The generated query constructs its own joint receipt and next inventory.
Its same physical trace fits the computed instruction and payload budgets.
The initial causal mass bound supplies every resource calculation.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointComputedQuery
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "Receipt" => SourceCurrentConstrainedCapCheckedJointInventoryQuery.Receipt
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {width mass : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A supplied joint receipt derives computed resources on its same physical trace and return. -/
theorem of_receipt (inventory : Inventory) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (before : Checked width) (good : Good before) (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (massStored : Stored mass before.native.machine.heap)
    (fuel : Nat) (value : Value Symbol Guard) (after : Checked width)
    (receipt : Receipt inventory depth formulas solver fuel left right before value after) :
    let bound := instructionBound before.native.machine.heap.nodes.next before.native.machine.heap.edges.next mass
    fuel ≤ bound ∧
      execute (bound + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after ∧
      Stored (massAfter bound mass) after.native.machine.heap ∧ InternedValueMass.value value ≤ massAfter bound mass ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit bound mass ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit bound mass ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + bound := by
  let source := before.native.machine.heap
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let bound := instructionBound source.nodes.next source.edges.next mass
  have facts := good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have count := SourceCurrentAllocatedNativeInstructionTrace.node_prefix source facts holds request scope complete
    receipt.trace good ready (grows_refl _) (extends_refl _)
  have initialCount := SourceCurrentAllocatedNativeComputedBudget.nodeBudget_le source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed massStored
  have enough : fuel ≤ bound := Nat.le_trans count initialCount
  have done := done_stable (fuel + 1) (bound - fuel)
    (.code (requestNode request.domain request.left request.right)) before after value receipt.done
  have sameFuel : fuel + 1 + (bound - fuel) = bound + 1 := by omega
  rw [sameFuel] at done
  obtain ⟨_inputs, _certificate, _lastGood, _fields, lastStored, lastNodes, lastEdges, lastDomains⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.prefix_bound receipt.trace good (fun _ => trivial) massStored
      (SourceRecursiveIntersectionCodeMass.request_node request.domain request.left request.right before.native.machine mass ready)
  have massBound := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono enough mass
  have credits := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono enough mass
  have resultMass := InternedValueMassHeap.available after.native.machine.heap lastStored value receipt.result
  exact ⟨enough, done, lastStored.mono massBound, Nat.le_trans resultMass massBound,
    Nat.le_trans lastNodes (Nat.add_le_add_left credits _),
    Nat.le_trans lastEdges (Nat.add_le_add_left credits _),
    Nat.le_trans lastDomains (Nat.add_le_add_left enough _)⟩

/-- Initial generated operands construct their joint receipt and computed resources at one exact return. -/
theorem generated_complete (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (good : Good before)
    (current : At formulas solver inventory before)
    (semantic : SemanticReady before.native.machine.heap)
    (context : Context Plain inventory.source before.native.machine)
    (stored : Joint Plain inventory.source before.native) (origins : Origins inventory.source before.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (massStored : Stored mass before.native.machine.heap)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap good.native.machine.1
      current.growth current.history left right leftAvailable rightAvailable leftClosed rightClosed
    let bound := instructionBound before.native.machine.heap.nodes.next before.native.machine.heap.edges.next mass
    ∃ fuel value after,
      Receipt next depth formulas solver fuel left right before value after ∧
      fuel ≤ bound ∧
      execute (bound + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after ∧
      Stored (massAfter bound mass) after.native.machine.heap ∧ InternedValueMass.value value ≤ massAfter bound mass ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit bound mass ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit bound mass ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + bound := by
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap good.native.machine.1
    current.growth current.history left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, receipt⟩ :=
    SourceCurrentConstrainedCapCheckedJointInventoryQuery.generated_complete bits depth formulas solver inventory before good
      current semantic context stored origins scopedCache idle left right leftAvailable rightAvailable leftClosed rightClosed
      leftCap rightCap nodes edges room
  exact ⟨fuel, value, after, receipt, of_receipt next depth formulas solver before good left right leftAvailable rightAvailable
    leftClosed rightClosed massStored fuel value after receipt⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointComputedQuery
