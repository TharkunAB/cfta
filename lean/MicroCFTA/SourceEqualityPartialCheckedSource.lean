import MicroCFTA.SourceEqualityPartialWorkerGraph

/-!
# Public language and replay from actual checked recursive execution

A successful bounded receipt and its actual reached checks derive the
complete recursive graph. Original closed normalized source construction
supplies the initial scope. Public language and stable replay then follow
without a callback law or a supplied completed graph. This result does not
assert success for every input or remove the native word-check boundary.
-/
namespace MicroCFTA.SourceEqualityPartialCheckedSource
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A checked success has its actual graph, identical replay, and exact contextual public meaning. -/
theorem contextual {width : Nat} (g e p h c n fuel : Nat)
    {inherited : SourceEqualityPrecheck.Constraint} {value result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel inherited value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok result) after)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ReduceNode inherited value before result after ∧ NodeRun inherited value before result after ∧
      SourceEqualityPartialGraphLaws.NodeLaw formulas solver ambient inherited value before result after := by
  have trace := SourceEqualityPartialWorkerGraph.graph g e p h c n fuel plan done
  exact ⟨trace, SourceEqualityPartialGraphExecution.node trace,
    SourceEqualityPartialGraphProofs.node formulas solver ambient trace⟩

/-- Actual successful public execution preserves all physical scope and exact public language. -/
theorem public_exact {width : Nat} (g e p h c n fuel : Nat)
    {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel (some []) value before = .done (.ok result) after)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧ NodeRun (some []) value before result after ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term :=
  SourceEqualityPartialSource.public_exact
    (SourceEqualityPartialWorkerGraph.graph g e p h c n fuel plan done) scope available closed formulas solver ambient

/-- Original closed source syntax supplies every checked successful public entry's exact language and stable execution. -/
theorem closed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Scope (cold width heap) ∧ Available heap value ∧ value.free = [] ∧
      ∀ g e p h c n fuel result after,
        SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value (cold width heap) →
        SourceEqualityPartialWorker.run g e p h c n fuel (some []) value (cold width heap) = .done (.ok result) after →
        Scope after ∧ SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧
          result.free = [] ∧ NodeRun (some []) value (cold width heap) result after ∧
          ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := SourceEqualityPartialSource.constructed width expression allowed value heap built
  exact ⟨value, heap, built, initial.1, initial.2.1, initial.2.2,
    fun g e p h c n fuel _ _ plan done =>
      public_exact g e p h c n fuel plan done initial.1 initial.2.1 initial.2.2 formulas solver ambient⟩

end MicroCFTA.SourceEqualityPartialCheckedSource
