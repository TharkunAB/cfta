import MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion
import MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion

/-!
# Exact language and cached closedness at one actual cold return

The contextual and scope inductions produce completed checked executions.
Determinism identifies their literal returned values and complete states.
The contextual receipt therefore also retains scoped memo tables and an
empty cached free-reference list for its root result.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Successful finite bounds cannot change the returned value or any checked state field. -/
theorem completed_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (firstFuel secondFuel : Nat) (control : Control A) (before firstAfter secondAfter : Checked width)
    (firstValue secondValue : A)
    (first : execute firstFuel control before = .done firstValue firstAfter)
    (second : execute secondFuel control before = .done secondValue secondAfter) :
    firstValue = secondValue ∧ firstAfter = secondAfter := by
  have firstStable := done_stable firstFuel secondFuel control before firstAfter firstValue first
  have secondStable := done_stable secondFuel firstFuel control before secondAfter secondValue second
  rw [Nat.add_comm secondFuel firstFuel] at secondStable
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- The same actual cold result has exact intersection language, scoped caches, and an empty free list. -/
theorem cold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width)) (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked width),
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) ⟨initial width machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver)
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨inputModel, inputRanked, fuel, value, after, receipt, idle, meaning⟩ :=
    SourceCurrentAllocatedNativeContextualCompletion.cold_complete formulas solver machine operations valid semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  obtain ⟨scopeFuel, scopedValue, scopedAfter, scopeReceipt, _, closed⟩ :=
    SourceCurrentAllocatedNativeScopeCompletion.cold_complete (SourceEqualityPCSGuard.holds formulas solver) machine operations
      valid semantic left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have same := completed_unique (fuel + 1) (scopeFuel + 1) _ _ after scopedAfter value scopedValue receipt.done scopeReceipt.done
  rcases same with ⟨rfl, rfl⟩
  exact ⟨inputModel, inputRanked, fuel, value, after, receipt, scopeReceipt.scopedCache, idle, closed, meaning⟩

end MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
