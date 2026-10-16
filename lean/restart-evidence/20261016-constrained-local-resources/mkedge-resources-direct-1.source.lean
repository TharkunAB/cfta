import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdge
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity

/-!
# Constructor resources for the checked parent edge

Both source branches execute one raw edge request and no node request.
The exact checked return retains native tables and their output profiles.
Initial headroom bounds the actual returned supplies.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdgeResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (observe nodeRequests edgeRequests makeEdge_observe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem output_stored
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : SourceCurrentAllocatedMkEdge.PhysicalReceipt formulas solver inventory before result after)
    (stored : OutputStored before.native) : OutputStored after.native := by
  constructor
  · simpa only [receipt.nodes] using stored.nodes
  · simpa only [receipt.edges] using stored.edges

private theorem edge_requests (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (heap : State Symbol Guard) :
    nodeRequests (observe (makeEdge symbol guard children) heap) = 0 ∧
      edgeRequests (observe (makeEdge symbol guard children) heap) = 1 := by
  simp [makeEdge_observe, nodeRequests, edgeRequests]

/-- Rejection constructs its sentinel and resources without a child or field premise. -/
theorem rejected (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (symbol : Symbol) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity : Nat)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2)) :
    let result := (SourceCurrentAllocatedMkEdge.reject symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject symbol before).2
    ∃ requests,
      SourceCurrentAllocatedMkEdge.RejectReceipt formulas solver inventory symbol before result after ∧
      NativeStored after.native ∧ OutputStored after.native ∧ EdgeShape rows (max arity 1) result ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 1 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  let result := (SourceCurrentAllocatedMkEdge.reject symbol before).1
  let after := (SourceCurrentAllocatedMkEdge.reject symbol before).2
  have receipt := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory symbol before ready admitted
  let requests := observe (makeEdge symbol top [.empty]) before.native.machine.heap
  have trace : Trace before.native.machine.heap after.native.machine.heap requests := .work _ _
  have counts := edge_requests symbol top [.empty] before.native.machine.heap
  have supply := SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_next symbol top [.empty] before.native.machine.heap
  have profile : EdgeShape rows (max arity 1) result := by
    change result.children.length ≤ max arity 1 ∧ ChildrenShape rows (max arity 1) result.children
    rw [receipt.children]
    exact ⟨Nat.le_max_right _ _, trivial, trivial⟩
  exact ⟨requests, receipt, SourceCurrentAllocatedFiniteOrdinaryMkEdge.native_stored receipt.toPhysicalReceipt native,
    output_stored receipt.toPhysicalReceipt output, profile, trace, counts.1, counts.2,
    ⟨by change (run (makeEdge symbol top [.empty]) before.native.machine.heap).2.nodes.next ≤ _; omega,
      by change (run (makeEdge symbol top [.empty]) before.native.machine.heap).2.edges.next ≤ _; omega⟩,
    supply.1, supply.2⟩

/-- Initial facts construct the full checked edge return and its single actual request. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (symbol : Symbol) (constraint : Allocated)
    (children : List (Value Symbol Guard)) (before : Checked (bits + 2))
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations (raw constraint))
    (available : Values before.native.machine.heap children)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity : Nat) (profile : ChildrenShape rows arity children) (lengthBound : children.length ≤ arity)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2)) :
    ∃ result after requests,
      SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint children before result after ∧
      NativeStored after.native ∧ OutputStored after.native ∧ EdgeShape rows (max arity 1) result ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 1 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  obtain ⟨result, after, receipt⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory symbol constraint children
    before ready admitted storedReady field available
  let keep := SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length
  let job := SourceEqualityMkEdgeAllocation.work symbol (raw constraint) children keep
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol constraint.stored constraint.guard children
    before.operations before.native.machine.heap ready.good.operations storedReady
  have heap : after.native.machine.heap = (run job before.native.machine.heap).2 := by
    have same := congrArg Prod.snd receipt.actual
    simp only [SourceCurrentAllocatedMkEdge.build, built.1] at same
    exact (congrArg (fun state => state.native.machine.heap) same).symm
  let requests := observe job before.native.machine.heap
  have trace : Trace before.native.machine.heap after.native.machine.heap requests := heap ▸ .work _ _
  have counts : nodeRequests requests = 0 ∧ edgeRequests requests = 1 := by
    cases value : keep <;> simpa only [requests, job, SourceEqualityMkEdgeAllocation.work, value, ↓reduceIte] using
      edge_requests symbol (if value = true then raw constraint else top) (if value = true then children else [.empty]) before.native.machine.heap
  have returned : EdgeShape rows (max arity 1) result := by
    change result.children.length ≤ max arity 1 ∧ ChildrenShape rows (max arity 1) result.children
    rw [receipt.children]
    cases selected : SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨Nat.le_max_right _ _, trivial, trivial⟩
    | true =>
        simp only [↓reduceIte]
        exact ⟨Nat.le_trans lengthBound (Nat.le_max_left _ _),
          ChildrenShape.mono children profile (Nat.le_refl _) (Nat.le_max_left _ _)⟩
  have supplies := trace.next_le
  have nodeExact := trace.next_exact
  have nodesSame : after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next := by
    have bounded := SourceCurrentAllocatedFiniteOrdinaryReservations.reservations_le_requests requests
    have nonnegative := Nat.zero_le (SourceCurrentAllocatedFiniteOrdinaryReservations.nodeReservations requests)
    rw [counts.1] at bounded
    omega
  exact ⟨result, after, requests, receipt, SourceCurrentAllocatedFiniteOrdinaryMkEdge.native_stored receipt.toPhysicalReceipt native,
    output_stored receipt.toPhysicalReceipt output, returned, trace, counts.1, counts.2,
    ⟨by omega, by omega⟩, nodesSame, by omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdgeResources
