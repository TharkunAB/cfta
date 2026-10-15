import MicroCFTA.SourceEqualityPartialInheritedPlainCompletion

/-!
# Finite exact equality-free source calls under arbitrary inherited payloads

Original source annotation checks derive the structural caller region.
Every inherited payload then has a completed actual graph, both source
gate memo receipts, preserved physical scope, and stable bounded execution.
Public output always narrows input. It is exact under inherited satisfaction.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainSource
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns SourceEqualityPartialMemoGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every inherited payload has finite complete region execution, exact contextual meaning, and both actual source memo tables. -/
theorem region_exact {width : Nat} {value : Value Symbol Guard} {before : NativeState width Symbol Guard}
    (plain : SourceEqualityPartialPlainRegion.Region value) (inherited : SourceEqualityPrecheck.Constraint)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ result after, ∃ trace : ReduceNode inherited value before result after, NodeReads trace ∧
      Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧ NodeRun inherited value before result after ∧
      ∀ term, (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term →
          InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) ∧
        (SourceEqualityPrecheck.Sat term inherited →
          (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term)) := by
  obtain ⟨result, after, trace⟩ := SourceEqualityPartialInheritedPlainCompletion.complete formulas solver ambient plain
    inherited before scope available closed
  have checked := SourceEqualityPartialGraphProofs.node formulas solver ambient trace scope available closed
  exact ⟨result, after, trace, SourceEqualityPartialMemoProofs.node formulas solver ambient trace scope available closed,
    checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, SourceEqualityPartialGraphExecution.node trace, checked.2.2.2.2⟩

/-- Original closed normalized equality-free syntax derives finite actual execution for every inherited payload at its independent guarded language. -/
theorem closed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (plain : SourceEqualityAnnotationConstruction.Allowed SourceEqualityPartialPlainAnnotations.NoEqualities expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∀ inherited, ∃ result after, ∃ trace : ReduceNode inherited value (cold width heap) result after, NodeReads trace ∧
        Scope after ∧ SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧
        result.free = [] ∧ NodeRun inherited value (cold width heap) result after ∧
        ∀ term, (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term →
            InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term) ∧
          (SourceEqualityPrecheck.Sat term inherited →
            (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
              InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term)) := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := SourceEqualityPartialSource.constructed width expression allowed value heap built
  have region := SourceEqualityPartialPlainAnnotations.constructed expression plain value heap built
  refine ⟨value, heap, built, ?_⟩
  intro inherited
  obtain ⟨result, after, trace, reads, scope, keeps, available, closed, replay, language⟩ :=
    region_exact region inherited initial.1 initial.2.1 initial.2.2 formulas solver ambient
  refine ⟨result, after, trace, reads, scope, keeps, available, closed, replay, ?_⟩
  intro term
  simpa only [InternedGuardedExecution.closed_language expression value heap built (acceptsConstraint formulas solver) ambient] using language term

end MicroCFTA.SourceEqualityPartialInheritedPlainSource
