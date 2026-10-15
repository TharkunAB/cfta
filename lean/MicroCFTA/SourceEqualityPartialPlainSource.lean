import MicroCFTA.SourceEqualityPartialPlainAnnotations

/-!
# Finite exact public reduction from equality-free original source syntax

Literal source guards derive the equality-free region. Structural
completion constructs the actual recursive graph. Its scope, source memo
receipts, exact public language, and stable bounded execution then follow.
No completed graph, successful worker receipt, or sufficient bound is given.
-/
namespace MicroCFTA.SourceEqualityPartialPlainSource
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns SourceEqualityPartialMemoGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Equality-free ordinary regions derive finite completed public execution, both memo receipts, and exact public language. -/
theorem region_exact {width : Nat} {value : Value Symbol Guard} {before : NativeState width Symbol Guard}
    (plain : SourceEqualityPartialPlainRegion.Region value)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ result after, ∃ trace : ReduceNode (some []) value before result after, NodeReads trace ∧
      Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧ NodeRun (some []) value before result after ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨result, after, trace⟩ := SourceEqualityPartialPlainCompletion.complete formulas solver ambient plain before scope available closed
  exact ⟨result, after, trace, SourceEqualityPartialMemoProofs.node formulas solver ambient trace scope available closed,
    SourceEqualityPartialSource.public_exact trace scope available closed formulas solver ambient⟩

/-- Original closed normalized equality-free syntax derives finite exact public execution at its independent guarded least language. -/
theorem closed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (plain : SourceEqualityAnnotationConstruction.Allowed SourceEqualityPartialPlainAnnotations.NoEqualities expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap result after, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      ∃ trace : ReduceNode (some []) value (cold width heap) result after, NodeReads trace ∧
        Scope after ∧ SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧
        result.free = [] ∧ NodeRun (some []) value (cold width heap) result after ∧
        ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
          InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := SourceEqualityPartialSource.constructed width expression allowed value heap built
  have region := SourceEqualityPartialPlainAnnotations.constructed expression plain value heap built
  obtain ⟨result, after, trace, reads, scope, keeps, available, closed, replay, language⟩ :=
    region_exact region initial.1 initial.2.1 initial.2.2 formulas solver ambient
  refine ⟨value, heap, result, after, built, trace, reads, scope, keeps, available, closed, replay, ?_⟩
  intro term
  simpa only [InternedGuardedExecution.closed_language expression value heap built (acceptsConstraint formulas solver) ambient] using language term

end MicroCFTA.SourceEqualityPartialPlainSource
