import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionComputedFuel
import MicroCFTA.SourceRecursiveIntersectionNumericSourceProfile

/-!
# Computed initial budgets for complete checked native queries

Initial source counters and causal payload mass bound the semantic fuel and
literal branching. Their instruction budget bounds the constructed query.
The same physical trace derives resources from the supplied payload bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeComputedBudget
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
variable {mass : Nat}

/-- Initial counters and stored payload mass give a computed instruction bound. -/
def instructionBound (nodes edges mass : Nat) : Nat :=
  SourceRecursiveIntersectionInstructionProfile.budget
    (SourceRecursiveIntersectionNumericSourceProfile.branching nodes edges mass)
    (SourceRecursiveIntersectionComputedFuel.ceiling nodes mass)

/-- Increasing any initial numeric parameter retains the instruction bound. -/
theorem instructionBound_mono {firstNodes lastNodes firstEdges lastEdges firstMass lastMass : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) (mass : firstMass ≤ lastMass) :
    instructionBound firstNodes firstEdges firstMass ≤ instructionBound lastNodes lastEdges lastMass :=
  SourceRecursiveIntersectionInstructionProfile.budget_parameters_mono
    (SourceRecursiveIntersectionNumericSourceProfile.branching_mono nodes edges mass)
    (SourceRecursiveIntersectionComputedFuel.ceiling_mono nodes mass)

variable [DecidableEq Symbol]

/-- Closed original operands derive their semantic instruction bound from initial numeric data. -/
theorem nodeBudget_le (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source) (holds : Guard → Language.Term Symbol → Bool)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) (stored : Stored mass source) :
    SourceCurrentAllocatedNativeInstructionTrace.nodeBudget source holds
      ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ≤ instructionBound source.nodes.next source.edges.next mass := by
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have fuel := SourceRecursiveIntersectionComputedFuel.initial_requiredFuel_le source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed stored complete
  rw [SourceCurrentAllocatedNativeInstructionTrace.nodeBudget_of_complete source holds _ complete]
  exact SourceRecursiveIntersectionInstructionProfile.budget_parameters_mono
    (SourceRecursiveIntersectionNumericSourceProfile.source_branching source stored) fuel

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial numeric data construct the complete query and resources on its exact returned state. -/
theorem initial (bits : Nat) (holds : Guard → Language.Term Symbol → Bool) (before : Checked (bits + 2))
    (good : Good before) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored mass before.native.machine.heap)
    (nodes : before.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.native.machine.domains.next +
      2 ^ (before.native.machine.heap.nodes.next + before.native.machine.heap.nodes.next * before.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
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
  obtain ⟨fuel, value, after, receipt, afterIdle, count, _remaining⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial bits holds before good semantic idle
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  have initialCount := nodeBudget_le before.native.machine.heap good.native.machine.1 holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed stored
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

end MicroCFTA.SourceCurrentAllocatedNativeComputedBudget
