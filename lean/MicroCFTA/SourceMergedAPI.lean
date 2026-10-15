import MicroCFTA.SourceMergedStability
import MicroCFTA.SourceMergedSource

/-!
# Finite general source merge and independent-language coverage

Original closed construction derives all merge input invariants. General
comparison and ordinary-height induction derive finite actual execution.
Every larger bound pair retains the identical value and complete cache.
-/
namespace MicroCFTA.SourceMergedAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open InternedGuardedLanguage (meaning)
open MergedOrdinaryHeight (height)
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One derived comparison bound stabilizes every ordinary bound above the original input height. -/
theorem saturated (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∃ bound result after, Effect before after ∧ Available after result ∧ result.free = [] ∧
      ∀ ordinary comparison, height value ≤ ordinary → bound ≤ comparison →
        SourceMergedWorker.worker MergedSourceGrouping.groups clear top ordinary comparison value before = .done result after := by
  obtain ⟨bound, result, after, done, effects, valid⟩ := SourceMergedCompletion.execute_complete clear top value before semantic available closed
  refine ⟨bound, result, after, effects, valid.1, valid.2, ?_⟩
  intro ordinary comparison ordinaryEnough comparisonEnough
  have repeated := SourceMergedStability.worker_refines MergedSourceGrouping.groups clear top (height value) ordinary ordinaryEnough
    bound (comparison - bound) value before result after (done bound (Nat.le_refl _))
  simpa only [Nat.add_sub_of_le comparisonEnough] using repeated

/-- Finite general merging retains every independent accepted input term and the actual complete cache. -/
theorem complete (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = []) :
    ∃ bound result after, Effect before after ∧ Available after result ∧ result.free = [] ∧
      (∀ ordinary comparison, height value ≤ ordinary → bound ≤ comparison →
        SourceMergedWorker.worker MergedSourceGrouping.groups clear top ordinary comparison value before = .done result after) ∧
      ∀ term, meaning holds ambient value term → meaning holds ambient result term := by
  obtain ⟨bound, result, after, effects, resident, resultClosed, stable⟩ := saturated clear top value before semantic available closed
  refine ⟨bound, result, after, effects, resident, resultClosed, stable, ?_⟩
  exact (SourceMergedSoundness.execute_covers clear top holds ambient clearTrue topTrue bound value before semantic available closed result after
    (stable (height value) bound (Nat.le_refl _) (Nat.le_refl _))).2.2.2

/-- Original closed source syntax has finite stable actual merging with independent source-language inclusion. -/
theorem source (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true) :
    ∃ value before bound result after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      Effect before after ∧ Available after result ∧ result.free = [] ∧
      (∀ ordinary comparison, height value ≤ ordinary → bound ≤ comparison →
        SourceMergedWorker.worker MergedSourceGrouping.groups clear top ordinary comparison value before = .done result after) ∧
      ∀ term, InternedGuardedSyntax.evaluate holds [] expression term → meaning holds ambient result term := by
  obtain ⟨value, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨bound, result, after, effects, available, closed, stable, covers⟩ := complete clear top holds ambient clearTrue topTrue value before
    (SourceEqualityRequiredSemanticCache.constructed expression value before built)
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value before built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built)
  refine ⟨value, before, bound, result, after, built, effects, available, closed, stable, ?_⟩
  intro term accepted
  apply covers term
  simpa only [InternedGuardedExecution.closed_language expression value before built holds ambient] using accepted

/-- Any two successful general source merge executions have the same value and full actual cache. -/
theorem successful_unique (clear : Guard → Bool) (top : Guard) (value first second : Value Symbol Guard)
    (before afterFirst afterSecond : State Symbol Guard) (firstOrdinary secondOrdinary firstComparison secondComparison : Nat)
    (firstDone : SourceMergedWorker.worker MergedSourceGrouping.groups clear top firstOrdinary firstComparison value before = .done first afterFirst)
    (secondDone : SourceMergedWorker.worker MergedSourceGrouping.groups clear top secondOrdinary secondComparison value before = .done second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  exact Prod.mk.inj (SourceMergedStability.successful_results_eq MergedSourceGrouping.groups clear top
    firstOrdinary secondOrdinary firstComparison secondComparison value before first second afterFirst afterSecond firstDone secondDone)

end MicroCFTA.SourceMergedAPI
