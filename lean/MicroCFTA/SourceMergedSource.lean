import MicroCFTA.SourceMergedSoundness
import MicroCFTA.SourceEqualityProjectionAPI

/-!
# Original source and projection entry to general merge coverage

Original construction derives every cache and closed-input premise.
Actual projection followed by a successful merge retains each selected
accepted subterm. General merge completion remains a separate obligation.
-/
namespace MicroCFTA.SourceMergedSource
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open InternedGuardedLanguage (meaning)

/-- Original closed source construction derives all premises of successful merge language coverage. -/
theorem source_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (value : Value Symbol Guard) (before : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value before)
    (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (comparisonFuel : Nat) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top comparisonFuel value before = .done result after) :
    Effect before after ∧ Available after result ∧ result.free = [] ∧
      ∀ term, InternedGuardedSyntax.evaluate holds [] expression term → meaning holds ambient result term := by
  have checked := SourceMergedSoundness.execute_covers clear top holds ambient clearTrue topTrue comparisonFuel value before
    (SourceEqualityRequiredSemanticCache.constructed expression value before built)
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value before built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built) result after done
  refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_⟩
  intro term accepted
  apply checked.2.2.2 term
  simpa only [InternedGuardedExecution.closed_language expression value before built holds ambient] using accepted

/-- Actual getPath and successful merging retain every accepted selected subterm through their exact caches. -/
theorem projection_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (path : List Int) (fuel readFuel comparisonFuel : Nat) (value projected result : Value Symbol Guard)
    (before middle after : State Symbol Guard) (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (projectedDone : SourceEqualityProjectionWorker.project fuel readFuel path value before = .done projected middle)
    (mergedDone : SourceMergedWorker.execute clear top comparisonFuel projected middle = .done result after) :
    Effect before after ∧ Available after result ∧ result.free = [] ∧
      ∀ term part, meaning holds ambient value term → SymbolicSignedPaths.lookup term path = some part → meaning holds ambient result part := by
  have projected := SourceEqualityProjectionAPI.node_done fuel readFuel path value projected before middle projectedDone semantic available closed
  have merged := SourceMergedSoundness.execute_covers clear top holds ambient clearTrue topTrue comparisonFuel _ middle
    projected.2.1 projected.2.2.1 projected.2.2.2.1 result after mergedDone
  exact ⟨(Effect.trans ⟨projected.1, projected.2.1⟩ merged.1), merged.2.1, merged.2.2.1,
    fun term part accepted selected => merged.2.2.2 part (projected.2.2.2.2 holds ambient term part accepted selected)⟩

end MicroCFTA.SourceMergedSource
