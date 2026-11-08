import MicroCFTA.SourceCurrentAllocatedNativeCreditWordRanges
import MicroCFTA.SourceCurrentAllocatedNativeComputedBudget

/-!
# Complete native queries with instruction-based domain capacity

Closed available operands derive their original source scope. Their initial
semantic instruction credit gives word admission for every actual prefix.
The same query then returns a physical receipt and resource bounds. The
computed variant uses only initial counters and stored payload mass.
The domain inventory cardinality is not a capacity premise.
These statements retain the modeled checked tables and their idle owners.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCreditCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceCurrentAllocatedNativeInstructionTrace (nodeBudget)
open SourceCurrentAllocatedNativeComputedBudget (instructionBound)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
variable {mass : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial physical caches, closed original roots, and numeric room construct a bounded complete query. -/
theorem initial (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      nodeBudget before.native.machine.heap holds ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ < 2 ^ (bits + 1)) :
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    let bound := nodeBudget before.native.machine.heap holds request
    ∃ fuel value after,
      Receipt fuel (.code (requestNode request.domain request.left request.right)) before value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ bound ∧
      execute (bound + 1) (.code (requestNode request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter bound (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      InternedValueMass.value value ≤ massAfter bound (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit bound (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit bound (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + bound := by
  let source := before.native.machine.heap
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have ranges := SourceCurrentAllocatedNativeCreditWordRanges.word_ranges bits holds before good semantic
    left right leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  have completeSemantic : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, receipt, bounds⟩ := SourceCurrentAllocatedNativeInitialInstructionBudget.complete source facts holds request
    (initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable)
    completeSemantic before good ⟨empty_domain _, leftAvailable, rightAvailable⟩
    (grows_refl _) (extends_refl _) (idle.active _ holds _ before.native) ranges
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ before after value
    (by intro result; trivial) good.native.shape idle receipt.done
  exact ⟨fuel, value, after, receipt, afterIdle, bounds⟩


/-- Initial numeric data construct the complete query and resources on its exact returned state. -/
theorem computed (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored mass before.native.machine.heap)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      instructionBound before.native.machine.heap.nodes.next before.native.machine.heap.edges.next mass < 2 ^ (bits + 1)) :
    let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
    let bound := instructionBound before.native.machine.heap.nodes.next before.native.machine.heap.edges.next mass
    ∃ fuel value after,
      Receipt fuel (.code (requestNode request.domain request.left request.right)) before value after
        (fun final result => Available final.heap result) ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ bound ∧
      execute (bound + 1) (.code (requestNode request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter bound mass) after.native.machine.heap ∧ InternedValueMass.value value ≤ massAfter bound mass ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit bound mass ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit bound mass ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + bound := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let bound := instructionBound before.native.machine.heap.nodes.next before.native.machine.heap.edges.next mass
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    good.native.machine.1.coherent rightAvailable rightClosed
  have initialCount := SourceCurrentAllocatedNativeComputedBudget.nodeBudget_le before.native.machine.heap good.native.machine.1 holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed stored
  have semanticRoom : before.native.machine.domains.next +
      nodeBudget before.native.machine.heap holds request < 2 ^ (bits + 1) :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left initialCount _) room
  obtain ⟨fuel, value, after, receipt, afterIdle, count, _remaining⟩ :=
    initial bits holds before good semantic idle left right leftAvailable rightAvailable leftClosed rightClosed nodes edges semanticRoom
  have enough : fuel ≤ bound := Nat.le_trans count initialCount
  have done := done_stable (fuel + 1) (bound - fuel)
    (.code (requestNode request.domain request.left request.right)) before after value receipt.done
  have sameFuel : fuel + 1 + (bound - fuel) = bound + 1 := by omega
  rw [sameFuel] at done
  have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  obtain ⟨_inputs, _certificate, _lastGood, _fields, lastStored, lastNodes, lastEdges, lastDomains⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.prefix_bound receipt.trace good (fun _ => trivial) stored
      (SourceRecursiveIntersectionCodeMass.request_node request.domain request.left request.right before.native.machine mass ready)
  have massBound := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono enough mass
  have credits := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono enough mass
  have resultMass := InternedValueMassHeap.available after.native.machine.heap lastStored value receipt.result
  exact ⟨fuel, value, after, receipt, afterIdle, enough, done, lastStored.mono massBound,
    Nat.le_trans resultMass massBound,
    Nat.le_trans lastNodes (Nat.add_le_add_left credits _),
    Nat.le_trans lastEdges (Nat.add_le_add_left credits _),
    Nat.le_trans lastDomains (Nat.add_le_add_left enough _)⟩


end MicroCFTA.SourceCurrentAllocatedNativeCreditCompletion
