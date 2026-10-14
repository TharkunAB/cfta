import MicroCFTA.SourceRecursiveIntersectionBudgetSoundness
import MicroCFTA.SourceRecursiveIntersectionBudgetCompleteness
import MicroCFTA.SourceRecursiveIntersectionGuardedInput
import MicroCFTA.InternedGuardedBudgetSupport

/-!
# Exact actual input languages at each unfolding budget

Closed available original records have exactly the finite input derivations
at each bound. Erasing the bound gives the independent guarded language.
This result does not assume budget preservation by stored reconstruction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionBudgetInput
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts IntersectSchedule
open SourceRecursiveIntersectionInputView

/-- A closed original record accepts exactly its actual input derivations at each bound. -/
theorem input_exact (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) (closed : value.free = [])
    (ambient : InternedGuardedBudget.Env Symbol) :
    InternedGuardedBudget.meaning holds ambient value =
      fun budget term => InputDerivation (view state holds) (inputOf value) budget term := by
  have noNames : freeNames value = [] := by simp only [freeNames, closed, List.filterMap_nil]
  let emptyEnv : InternedGuardedBudget.Env Symbol := fun _ _ _ => False
  have upward : ∀ name, BinderBudgetLanguage.Upward (emptyEnv name) := fun _ _ _ _ _ impossible => impossible
  rw [InternedGuardedBudget.closed_meaning holds value state facts.coherent available closed ambient emptyEnv]
  funext budget term
  apply propext
  constructor
  · apply original_sound state facts holds value original available emptyEnv
    intro name member
    rw [noNames] at member
    contradiction
  · apply original_complete state facts holds value original available budget emptyEnv upward
    intro name member
    rw [noNames] at member
    contradiction

/-- Erasing the actual input budget gives the independent stored least language. -/
theorem erase_exact (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) (closed : value.free = [])
    (ambient : InternedGuardedBudget.Env Symbol)
    (unbounded : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds unbounded value =
      fun term => ∃ budget, InternedGuardedBudget.meaning holds ambient value budget term := by
  rw [input_exact state facts holds value original available closed ambient]
  exact SourceRecursiveIntersectionGuardedInput.input_exact state facts holds value original available closed unbounded

end MicroCFTA.SourceRecursiveIntersectionBudgetInput
