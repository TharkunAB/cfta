import MicroCFTA.SourceEqualityPartialGraphProofs
import MicroCFTA.SourceEqualityPartialGraphExecution

/-!
# Original closed source entry for completed partial-reduction graphs

Original normalized source syntax derives its physical heap, available
closed value, and initial native scope. Every completed outer graph then
has exact public language and stable actual bounded execution. Existence
of such an outer graph remains a separate caller termination obligation.
-/
namespace MicroCFTA.SourceEqualityPartialSource
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard

/-- Actual original construction derives every initial recursive scope premise. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression) (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    Scope (cold width heap) ∧ Available heap value ∧ value.free = [] := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have annotations : SourceEqualityAnnotationHeap.Heap validGuard heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceEqualityAnnotationConstruction.build validGuard expression allowed [] empty (SourceEqualityAnnotationHeap.empty_heap validGuard)
  have probes := SourceEqualityPartialProbeEntry.constructed expression value heap built
  exact ⟨⟨SourceEqualityNativeInitial.ready width top conjoin heap semantic, annotations, probes⟩,
    (InternedFreshOrdinaryFacts.closed_verified expression).result value heap built,
    InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built⟩

/-- A completed actual public entry preserves exact public language and both physical heaps without a callback-law premise. -/
theorem public_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (trace : ReduceNode (some []) value before result after) (scope : Scope before)
    (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol) :
    Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
      NodeRun (some []) value before result after ∧ ∀ term,
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient trace scope available closed
  refine ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, SourceEqualityPartialGraphExecution.node trace, ?_⟩
  intro term
  exact (checked.2.2.2.2 term).2 (by simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies])

/-- Closed normalized source syntax completes construction and supplies every completed caller graph's exact stable public entry. -/
theorem closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Scope (cold width heap) ∧ Available heap value ∧ value.free = [] ∧
      ∀ result after, ReduceNode (some []) value (cold width heap) result after →
        Scope after ∧ SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
          NodeRun (some []) value (cold width heap) result after ∧ ∀ term,
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
              InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := constructed width expression allowed value heap built
  exact ⟨value, heap, built, initial.1, initial.2.1, initial.2.2,
    fun _ _ graph => public_exact graph initial.1 initial.2.1 initial.2.2 formulas solver ambient⟩

end MicroCFTA.SourceEqualityPartialSource
