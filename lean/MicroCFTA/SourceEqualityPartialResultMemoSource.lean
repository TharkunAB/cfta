import MicroCFTA.SourceEqualityPartialResultMemoProofs
import MicroCFTA.SourceEqualityPartialSource

/-!
# Original source construction and actual memo-aware public reduction

Construction derives the closed input, native scope, and empty result memo.
A successful checked execution retains every completed-cell proof and the
exact public language. Successful execution is not proved for all inputs.
The preserved fixture reaches busy before either caller completes.
-/
namespace MicroCFTA.SourceEqualityPartialResultMemoSource
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame SourceEqualityPartialMemoSound
open SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Original closed source construction derives the full memo-aware public entry premises. -/
theorem constructed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    Sound holds ambient (initial (SourceEqualityNativeInitial.cold width heap)) ∧
      Scope (SourceEqualityNativeInitial.cold width heap) ∧ Available heap value ∧ value.free = [] :=
  ⟨initial_sound holds ambient _, SourceEqualityPartialSource.constructed width expression allowed value heap built⟩

/-- The actual completed memo-aware public caller preserves exact original language and all cell provenance. -/
theorem public_exact (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (g e p h c n fuel : Nat)
    (result : Value Symbol Guard) (after : SourceEqualityPartialMemoWorker.State width)
    (plan : SourceEqualityPartialResultMemoProofs.Checked g e p h c n fuel (some []) value
      (initial (SourceEqualityNativeInitial.cold width heap)))
    (done : SourceEqualityPartialMemoWorker.run g e p h c n fuel (some []) value
      (initial (SourceEqualityNativeInitial.cold width heap)) = .done (.ok result) after) :
    Sound (acceptsConstraint formulas solver) ambient after ∧ Scope after.native ∧
      SourceEqualityRequiredCache.Keeps heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  have entry := constructed width expression allowed value heap built (acceptsConstraint formulas solver) ambient
  exact SourceEqualityPartialResultMemoProofs.public_exact formulas solver ambient g e p h c n fuel value
    (initial (SourceEqualityNativeInitial.cold width heap)) result after plan entry.1 entry.2.1 entry.2.2.1 entry.2.2.2 done

end MicroCFTA.SourceEqualityPartialResultMemoSource
