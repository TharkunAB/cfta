import MicroCFTA.SourceCurrentAllocatedNativeInstructionTrace
import MicroCFTA.SourceCurrentAllocatedNativeWidthTrace
import MicroCFTA.SourceCurrentAllocatedRecursiveMassMonotone
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

/-!
# Complete checked queries with initial instruction and payload budgets

The original source fixes semantic rank and branching. The constructed
physical trace spends that initial credit. Its exact returned heap, native
tables, and equality operations also satisfy the initial payload schedule.
Closed original roots derive word admission from initial counters and room.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceCurrentAllocatedNativeInstructionTrace (nodeBudget)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "initialBound" => InternedValueMassHeap.initialBound
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A complete original query constructs its own trace and fits the initial source instruction budget. -/
theorem complete (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (semantic : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request))
    (before : Checked width) (good : Good before) (ready : NodeReady before.native.machine request)
    (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (active : SourceRecursiveIntersectionNative.ActiveAbove (view source holds) holds
      (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) semantic + 1) before.native)
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode request.domain request.left request.right)) before) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode request.domain request.left request.right)) before value after
        (fun final result => Available final.heap result) ∧
      fuel ≤ nodeBudget source holds request ∧
      execute (nodeBudget source holds request + 1) (.code (requestNode request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter (nodeBudget source holds request) (initialBound before.native.machine.heap)) after.native.machine.heap ∧
      InternedValueMass.value value ≤ massAfter (nodeBudget source holds request) (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next +
        credit (nodeBudget source holds request) (initialBound before.native.machine.heap) ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next +
        credit (nodeBudget source holds request) (initialBound before.native.machine.heap) ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + nodeBudget source holds request := by
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativePhysicalTraceCompletion.request_complete
    source facts holds request scope semantic before good ready growth history active ranges
  have count := SourceCurrentAllocatedNativeInstructionTrace.node_prefix source facts holds request scope semantic
    receipt.trace good ready growth history
  have exactResult := done_stable (fuel + 1) (nodeBudget source holds request - fuel)
    (.code (requestNode request.domain request.left request.right)) before after value receipt.done
  have sameFuel : fuel + 1 + (nodeBudget source holds request - fuel) = nodeBudget source holds request + 1 := by omega
  rw [sameFuel] at exactResult
  have physical := SourceCurrentAllocatedNativeWidthTrace.node_return request value receipt.trace good ready
  have largerMass := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono count (initialBound before.native.machine.heap)
  have largerCredit := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono count (initialBound before.native.machine.heap)
  exact ⟨fuel, value, after, receipt, count, exactResult, physical.2.1.mono largerMass,
    Nat.le_trans physical.2.2.1 largerMass,
    Nat.le_trans physical.2.2.2.1 (Nat.add_le_add_left largerCredit _),
    Nat.le_trans physical.2.2.2.2.1 (Nat.add_le_add_left largerCredit _),
    Nat.le_trans physical.2.2.2.2.2 (Nat.add_le_add_left count _)⟩

/-- Initial physical caches, closed original roots, and numeric room construct a bounded complete query. -/
theorem initial (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
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
  have ranges := SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before good semantic
    left right leftOriginal rightOriginal leftAvailable rightAvailable nodes edges room
  have completeSemantic : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, receipt, bounds⟩ := complete source facts holds request
    (initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable)
    completeSemantic before good ⟨empty_domain _, leftAvailable, rightAvailable⟩
    (grows_refl _) (extends_refl _) (idle.active _ holds _ before.native) ranges.1
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ before after value
    (by intro result; trivial) good.native.shape idle receipt.done
  exact ⟨fuel, value, after, receipt, afterIdle, bounds⟩

end MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
