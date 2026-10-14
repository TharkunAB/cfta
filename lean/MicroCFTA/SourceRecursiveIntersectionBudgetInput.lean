import MicroCFTA.SourceRecursiveIntersectionInputLanguage
import MicroCFTA.InternedGuardedBudget

/-!
# Original input environments at a fixed unfolding budget

The stored interpretation and actual input derivations use the same bound.
Free references retain explicit soundness and completeness premises.
-/
namespace MicroCFTA.SourceRecursiveIntersectionBudgetInput
open Language InternedConstructorTemplates InternedBinderProtocol IntersectSchedule
open SourceRecursiveIntersectionInputView

/-- Free reference languages contain only actual derivations at the same budget. -/
def SoundEnvironment (state : State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (environment : InternedGuardedBudget.Env Symbol) : Prop :=
  ∀ name ∈ freeNames value, ∀ budget term,
    environment (.interned name) budget term → InputDerivation (view state holds) (.ref name) budget term

/-- Free reference languages contain all actual derivations through the given bound. -/
def CompleteEnvironment (state : State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (budget : Nat) (environment : InternedGuardedBudget.Env Symbol) : Prop :=
  ∀ name ∈ freeNames value, ∀ smaller, smaller ≤ budget → ∀ term,
    InputDerivation (view state holds) (.ref name) smaller term → environment (.interned name) smaller term

end MicroCFTA.SourceRecursiveIntersectionBudgetInput
