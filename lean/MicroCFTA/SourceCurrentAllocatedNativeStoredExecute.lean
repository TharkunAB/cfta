import MicroCFTA.SourceCurrentAllocatedNativeStoredPrefix
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Native certificates in actual bounded node execution

The public laws use current entry facts. They have no trace premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredExecute
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedFiniteOrdinaryStored
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Node" => Value Symbol Guard
local notation "checkedInitial" => SourceCurrentAllocatedPartialInitialization.checked
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Bounded execution returns a state from its own checked return trace. -/
private theorem execute_state_prefix {Output : Type}
    {length : Nat} {control : Control Output} {before final : Checked width} {value : Output}
    (trace : Trace length control before (.code (.pure value)) final) (fuel : Nat) :
    ∃ prefixFuel remaining current,
      Trace prefixFuel control before remaining current ∧
        (execute fuel control before).state = current := by
  induction fuel generalizing length control before with
  | zero => exact ⟨0, control, before, .refl _ _, rfl⟩
  | succ fuel ih =>
      cases trace with
      | refl => exact ⟨0, _, _, .refl _ _, rfl⟩
      | cons start entry next middle last result count inputs one tail =>
          obtain ⟨prefixFuel, remaining, current, checked, observed⟩ := ih tail
          refine ⟨prefixFuel + 1, remaining, current,
            Trace.cons _ _ _ _ _ _ prefixFuel inputs one checked, ?_⟩
          simpa only [SourceEqualityNativeDemand.execute, one] using observed

/-- Every actual bounded root query retains native certificates from its current entry. -/
theorem execute_stored (bits : Nat) (before : Checked (bits + 2))
    (left right : Node) (fuel : Nat)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored before.native)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next +
        before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
    Stored (execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before).state.native := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before
    ready.good ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable nodes edges room).1
  obtain ⟨length, value, after, receipt, _⟩ :=
    SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete (fun _ _ => true) before ready.good ready.idle
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  obtain ⟨prefixFuel, remaining, current, checked, observed⟩ := execute_state_prefix receipt.trace fuel
  rw [observed]
  exact SourceCurrentAllocatedNativeStoredPrefix.node_prefix_stored
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before current prefixFuel remaining checked
    ready.good ready.semantic stored

/-- The literal checked initializer supplies the native entry certificates. -/
theorem initial_execute_stored (bits : Nat)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (left right : Node) (fuel : Nat)
    (ready : SourceCurrentConjunctionClassScan.Ready (checkedInitial (bits + 2) cache heap))
    (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : heap.nodes.next < 2 ^ bits) (edges : heap.edges.next ≤ 2 ^ (bits + 2))
    (room : (checkedInitial (bits + 2) cache heap).native.machine.domains.next +
      2 ^ (heap.nodes.next + heap.nodes.next * heap.nodes.next) < 2 ^ (bits + 1)) :
    Stored (execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (checkedInitial (bits + 2) cache heap)).state.native :=
  execute_stored bits (checkedInitial (bits + 2) cache heap) left right fuel ready
    leftAvailable rightAvailable leftClosed rightClosed
    (initial_stored (bits + 2) ⟨heap, Cache.emptyState⟩) nodes edges room

end MicroCFTA.SourceCurrentAllocatedNativeStoredExecute
