import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory
import MicroCFTA.SourceRecursiveIntersectionNativeFiniteObservation
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RecursiveSemanticProgressChecks
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedNativePhysicalCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Arbitrary repaired closed syntax derives current physical inputs before any native query. -/
theorem constructed_current_inputs [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) {initial final : Cache.State SourceEqualityPartialConstraintKey.Key}
    {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial final originals)
    (valid : Cache.Valid initial) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals) :
    ∃ value heap, InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap ∧
      Good (⟨SourceRecursiveIntersectionThunks.initial width ⟨heap, Cache.emptyState⟩,
        SourceEqualityConstraintMemoAllocation.initial final⟩ : SourceEqualityNativeDemand.State width) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady heap ∧ Available heap value ∧ value.free = [] ∧
      SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, heap, built,
    SourceCurrentAllocatedNativeOriginalHistory.constructed width history valid expression covered value heap built⟩

/-- Current warm completion derives Original and retains the actual equality-operation state. -/
theorem current_query_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (before : SourceEqualityNativeDemand.State width)
    (good : Good before) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (left right : Value Symbol Guard) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right) (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before) :
    ∃ fuel value after,
      SourceEqualityNativeDemand.execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after ∧
      Good after ∧ SourceRecursiveIntersectionNative.Idle after.native ∧ Available after.native.machine.heap value ∧
      Extension before.native.machine after.native.machine ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    good.native.machine.1.coherent rightAvailable rightClosed
  obtain ⟨fuel, value, after, receipt, afterIdle⟩ :=
    SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete holds before good idle left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel + 1, value, after, receipt.done, receipt.good, afterIdle, receipt.result,
    receipt.extension, receipt.operations⟩

/-- Reset can increase the remaining-pair count, so that count alone is not a measure. -/
theorem reset_increases_unseen :
    (IntersectSchedule.unseen [(0, 0)] (⟨[(0, .mu 0)], [(0, 0)]⟩ : IntersectSchedule.Domain)).length <
      (IntersectSchedule.unseen [(0, 0)] ({} : IntersectSchedule.Domain)).length := by
  decide

#print axioms constructed_current_inputs
#check @constructed_current_inputs
#print axioms current_query_done
#check @current_query_done
#print axioms reset_increases_unseen
#check @reset_increases_unseen
end MicroCFTA.RecursiveSemanticProgressChecks
