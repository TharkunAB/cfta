import MicroCFTA.SourceFreshOrdinarySizedEntry

/-!
# Complete exact reference and optimized Sized entry from repaired construction

Actual cold conversion supplies normalized validated rows. Original checked
annotations derive their equality invariant. Both query paths return the
same complete result at the independent original physical language.
-/
namespace MicroCFTA.SourceFreshOrdinarySizedEntry
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceObservations SourceSymbolicIndex SourceGuards SourceSizedFiniteKeys
open SourceFreshOrdinaryLiquidEntry (rawRows queryRows)
open SourcePreparedSharedRows (encode)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "C" => InternedConstructorTemplates.State Symbol Guard
local notation "V" => InternedConstructorTemplates.Value Symbol Guard
local notation "Api" => SourceSizedDispatcher.Api Symbol
local notation "Active" => (fun constraint : SourceSymbolicIndex.Constraint FullSyntax.Formula =>
  SourceCompactGuards.ActiveOption (SourceSymbolicIndex.Constraint.equalities constraint))

variable [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (dispatch : Bool) (value : V)

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- Actual finite cold conversion supplies a complete reference or optimized public result. -/
theorem complete (state : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value) :
    ∃ result final, Execution dispatch value state result final := by
  by_cases closed : value.free = []
  · obtain ⟨rows, final, _, _, trace, _, _, _, _, _, _, _, _, _, domain, _⟩ :=
      SourceFreshOrdinaryColdSharedRows.cold_table state semantic covered heap value available closed
    cases checked : FTAValidation.mkFTA (encode value)
        (interpreted (rawRows rows (keys final rows) value) (fun _ _ => true)) with
    | error error =>
        exact ⟨.error (.invalidFTA error), final, .invalid state final rows (keys final rows) domain closed trace error checked⟩
    | ok output =>
        have same := FTAValidation.mkFTA_returns (encode value)
          (interpreted (rawRows rows (keys final rows) value) (fun _ _ => true)) output checked
        have success : FTAValidation.mkFTA (encode value)
            (interpreted (rawRows rows (keys final rows) value) (fun _ _ => true)) =
            .ok (interpreted (queryRows rows (keys final rows) value) (fun _ _ => true)) := by
          rw [checked, same]
          exact congrArg Except.ok (normalized_interpreted _ _).symm
        exact ⟨_, final, .returned state final rows (keys final rows) domain closed trace success⟩
  · exact ⟨.error .openNode, state, .openRoot state closed⟩

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- Every failed actual closed conversion is the real source arity error. -/
theorem Execution.invalid_arity (state final : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (result : Result) (actual : Execution dispatch value state result final)
    (error : FTAValidation.Error SourceInternedRows.State Symbol) (failed : result = .error (.invalidFTA error)) :
    ∃ arity, error = .inconsistent arity := by
  cases actual with
  | openRoot isOpen => cases failed
  | invalid final rows keys domain closed trace sourceError checked =>
      have same := SourceInternedRows.ViewError.invalidFTA.inj (Except.error.inj failed)
      subst error
      exact trace.builder_error state final value rows semantic covered available closed keys domain sourceError checked
  | returned final rows keys domain closed trace checked => cases failed

/-- Every successful actual reference or optimized result has the exact original guarded root language. -/
theorem Execution.exact_queries (state final : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (constraints : InternedFreshOrdinaryConstraintHeap.Heap Active state) (available : Available state value)
    (result : Result) (api : Api) (actual : Execution dispatch value state result final)
    (success : result = .ok (.ok api)) (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    SourceSizedApiLaws.Exact api (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value) := by
  cases actual with
  | openRoot isOpen => cases success
  | invalid final rows keys domain closed trace error checked => cases success
  | returned final rows keys domain closed trace checked =>
      have queried := Except.ok.inj success
      rw [queries_reference dispatch (queryRows rows keys value) (encode value)
        (normalized_validated (rawRows rows keys value) (encode value) checked)] at queried
      have active := trace.normalized_constraints state final value rows semantic covered available closed Active constraints keys domain
      have exactQueries := SourceSizedFiniteKeysPublic.native_reference_exact (queryRows rows keys value) (encode value)
        (normalized_validated (rawRows rows keys value) (encode value) checked) active formulas solver api queried
      have language (term : Term Symbol) :
          Accepts (SourceSizedDecided.automaton (lookup (queryRows rows keys value)) (acceptsConstraint formulas solver))
            (encode value) term ↔ InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
        unfold queryRows rawRows
        rw [normalized_graph, SourceColdSharedRows.sized_graph]
        exact SourceFreshOrdinaryColdGuardedExact.trace_table_exact state final value rows trace semantic covered
          guarded budgetHeap available closed keys domain _ ambient term
      have sameLanguage : Accepts (SourceSizedDecided.automaton (lookup (queryRows rows keys value)) (acceptsConstraint formulas solver))
          (encode value) = InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value :=
        funext (fun term => propext (language term))
      rw [sameLanguage] at exactQueries
      exact exactQueries

/-- Both actual paths finish at the identical cache with the identical complete result and exact query laws. -/
theorem complete_both_exact (state : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (constraints : InternedFreshOrdinaryConstraintHeap.Heap Active state) (available : Available state value)
    (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula) :
    ∃ result final, Execution false value state result final ∧ Execution true value state result final ∧
      ∀ api, result = .ok (.ok api) → ∀ ambient,
        SourceSizedApiLaws.Exact api (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value) := by
  obtain ⟨result, final, actual⟩ := complete false value state semantic covered heap available
  exact ⟨result, final, actual, actual.change_dispatch false true value state final result,
    fun api success ambient => actual.exact_queries false value state final semantic covered guarded budgetHeap constraints available
      result api success formulas solver ambient⟩

omit dispatch in
/-- Actual checked closed construction derives every internal premise for both complete exact public Sized paths. -/
theorem constructed_complete (expression : InternedNestedConstruction.Syntax Symbol Guard) (state : C)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid Active expression)
    (formulas : Formulas FullSyntax.Formula) (solver : Entailment FullSyntax.Formula) :
    ∃ result final, Execution false value state result final ∧ Execution true value state result final ∧
      ∀ api, result = .ok (.ok api) → ∀ ambient,
        SourceSizedApiLaws.Exact api (InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value) := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value state built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have heap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  have constraints : InternedFreshOrdinaryConstraintHeap.Heap Active state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap Active expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap Active) annotations
  exact complete_both_exact value state semantic covered heap guarded budgetHeap constraints available formulas solver

end MicroCFTA.SourceFreshOrdinarySizedEntry
