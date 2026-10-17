import MicroCFTA.SourceCurrentConstrainedCapCheckedJointClosed

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 1000000

namespace MicroCFTA.CheckedJointClosedIndependentKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial numeric resources produce the literal full checked return and its exact language and joint laws. -/
theorem literal_joint_return (bits depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady machine.heap)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1)) :
    ∃ (fuel : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
      execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial (bits + 2) machine, operations⟩ = .done value after ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧
      Extension machine after.native.machine ∧
      SourceEqualityConstraintMemoAllocation.Grows operations after.operations ∧
      SourceCurrentConstrainedCapKernelJoint.Context Plain machine.heap after.native.machine ∧
      SourceCurrentConstrainedCapCheckedJointCache.Stored Plain machine.heap after.native ∧
      SourceCurrentConstrainedCap.Cap Plain depth value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight Plain machine.heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank Plain left right) value ∧
      value.free = [] ∧ Original value ∧ SourceCurrentConstrainedCapNativeProbeSupport.ProbeFree value ∧
      (∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term) := by
  obtain ⟨model, ranked, fuel, value, after, receipt, _scoped, _idle, closed, meaning,
      context, stored, cap, classified, original, probeFree, _current⟩ :=
    SourceCurrentConstrainedCapCheckedJointClosed.cold_complete bits depth formulas solver machine operations good
      semantic guards left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
      leftCap rightCap nodes edges room
  exact ⟨fuel + 1, value, after, receipt.done, receipt.good, receipt.extension,
    receipt.operations, context, stored, cap, classified, closed, original, probeFree, meaning⟩

#print axioms literal_joint_return
#check @literal_joint_return
end MicroCFTA.CheckedJointClosedIndependentKernels
