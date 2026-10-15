import MicroCFTA.SourceEqualityPartialMemoProofs

/-!
# Original public checked execution with complete source memo receipts

Closed normalized construction supplies the initial physical scope. Every
checked successful public worker receipt derives its recursive graph and
both source gate memo tables, exact public language, and stable replay.
General outer success and the outer reduction memo table remain separate.
-/
namespace MicroCFTA.SourceEqualityPartialMemoSource
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphRuns SourceEqualityPartialMemoGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "validGuard" => SourceEqualityNormalizedEntry.ValidGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual checked public success has both gate memo receipts, exact language, and identical full-state replay. -/
theorem public_exact {width : Nat} (g e p h c n fuel : Nat)
    {value result : Value Symbol Guard} {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel (some []) value before = .done (.ok result) after)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ trace : ReduceNode (some []) value before result after, NodeReads trace ∧
      Scope after ∧ SourceEqualityRequiredCache.Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧ NodeRun (some []) value before result after ∧
      ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  let trace := SourceEqualityPartialWorkerGraph.graph g e p h c n fuel plan done
  exact ⟨trace, SourceEqualityPartialMemoProofs.node formulas solver ambient trace scope available closed,
    SourceEqualityPartialCheckedSource.public_exact g e p h c n fuel plan done scope available closed formulas solver ambient⟩

/-- Original closed normalized syntax derives every successful public entry's actual memo evidence and exact stable result. -/
theorem closed (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : SourceEqualityAnnotationConstruction.Allowed validGuard expression)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Scope (cold width heap) ∧ Available heap value ∧ value.free = [] ∧
      ∀ g e p h c n fuel result after,
        SourceEqualityPartialChecks.Checked g e p h c n fuel (some []) value (cold width heap) →
        SourceEqualityPartialWorker.run g e p h c n fuel (some []) value (cold width heap) = .done (.ok result) after →
        ∃ trace : ReduceNode (some []) value (cold width heap) result after, NodeReads trace ∧
          Scope after ∧ SourceEqualityRequiredCache.Keeps heap after.machine.heap ∧ Available after.machine.heap result ∧
          result.free = [] ∧ NodeRun (some []) value (cold width heap) result after ∧
          ∀ term, InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient result term ↔
            InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have initial := SourceEqualityPartialSource.constructed width expression allowed value heap built
  exact ⟨value, heap, built, initial.1, initial.2.1, initial.2.2,
    fun g e p h c n fuel _ _ plan done =>
      public_exact g e p h c n fuel plan done initial.1 initial.2.1 initial.2.2 formulas solver ambient⟩

end MicroCFTA.SourceEqualityPartialMemoSource
