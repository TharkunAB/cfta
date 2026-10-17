import MicroCFTA.SourceCurrentNativeEdgeWriterGrowth
import MicroCFTA.SourceCurrentAllocatedNativeComputedBudget
import MicroCFTA.SourceCurrentAllocatedConjunctionMemo

/-!
# Initial callers produce persistent native writer histories

Initial numeric resources construct the actual native query and its history.
Initial conjunction invariants construct the physical advance and its growth.
Neither caller supplies a future trace, result, or writer law.
These two entry results retain their separate input domains.
-/
namespace MicroCFTA.SourceCurrentNativeCausalEntry
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceCurrentAllocatedNativeComputedBudget (instructionBound)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
variable {mass width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial closed operands and numeric resources construct the query and its exact writer history. -/
theorem query (bits : Nat) (holds : Guard → Term Symbol → Bool) (before : Checked (bits + 2))
    (history : History before) (good : Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
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
      History after ∧ SourceRecursiveIntersectionNative.Idle after.native ∧ fuel ≤ bound ∧
      execute (bound + 1) (.code (requestNode request.domain request.left request.right)) before = .done value after ∧
      Stored (massAfter bound mass) after.native.machine.heap ∧ InternedValueMass.value value ≤ massAfter bound mass ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + credit bound mass ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + credit bound mass ∧
      after.native.machine.domains.next ≤ before.native.machine.domains.next + bound := by
  obtain ⟨fuel, value, after, receipt, afterIdle, count, done, afterStored, valueMass, nodeCount, edgeCount, domainCount⟩ :=
    SourceCurrentAllocatedNativeComputedBudget.initial bits holds before good semantic idle
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed stored nodes edges room
  exact ⟨fuel, value, after, receipt,
    history.query ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ fuel value good receipt.trace,
    afterIdle, count, done, afterStored, valueMass, nodeCount, edgeCount, domainCount⟩

/-- Initial conjunction data construct the physical advance and preserve the same captured writers. -/
theorem conjunction [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (value : Value Symbol Guard) (before : Checked width)
    (history : History before) (good : Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (available : Available before.native.machine.heap value)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call budget memo value (physical before) answer after saved ∧
      SourceCurrentAllocatedConjunctionMemo.Receipt before after ∧
      History (advancePhysical before after) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver value answer ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨answer, after, saved, actual, receipt, finalCorrect, sound, retained⟩ :=
    SourceCurrentAllocatedConjunctionMemo.finite formulas solver budget memo value before
      good semantic costs idle available correct
  exact ⟨answer, after, saved, actual, receipt,
    .advance history after receipt.effects.keeps.growth, finalCorrect, sound, retained⟩

end MicroCFTA.SourceCurrentNativeCausalEntry
