import MicroCFTA.SourceFreshOrdinaryLiquidEntry

/-!
# Finite complete public liquid Sized entry from repaired construction

Actual execution retains conversion, solver exception, and Unknown outcomes.
Every successful query record has the independent guarded language of the
original physical root. Closed construction derives the required heaps.
-/
namespace MicroCFTA.SourceFreshOrdinaryLiquidEntry
open Cache Language RecursiveSize InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceObservations SourceSymbolicIndex SourceSizedFiniteKeys
open SolverAdapter SourceSizedLiquidProgram
open SourcePreparedSharedRows (encode)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "C" => InternedConstructorTemplates.State Symbol Guard
local notation "V" => InternedConstructorTemplates.Value Symbol Guard
local notation "Api" => SourceSizedDispatcher.Api Symbol

variable [Ord Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (milliseconds : Int)
    (check : Prepared → Nat → Attempt → Prop) (bound : Int) (value : V)

/-- Finite external attempts suffice for the actual staged source outcome, including validation failures. -/
theorem complete (state : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state) (available : Available state value)
    (completed : ∀ request, ∃ work attempt, check request work attempt) :
    ∃ result final, Execution given assumptions milliseconds check bound value state result final := by
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
        obtain ⟨result, work, run⟩ := SourceSizedFiniteKeysNativeLiquid.encoded_finite
          (queryRows rows (keys final rows) value) (encode value)
          (normalized_validated _ _ success) given assumptions milliseconds check completed bound
        exact ⟨_, final, .returned state final rows (keys final rows) domain closed trace success result work run⟩
  · exact ⟨.error .openNode, state, .openRoot state closed⟩

variable [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- A failed actual closed conversion has exactly an arity error before any solver fold. -/
theorem Execution.invalid_arity (state final : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (result : Result)
    (actual : Execution given assumptions milliseconds check bound value state result final)
    (error : FTAValidation.Error SourceInternedRows.State Symbol) (failed : result = .error (.invalidFTA error)) :
    ∃ arity, error = .inconsistent arity := by
  cases actual with
  | openRoot isOpen => cases failed
  | invalid final rows keys domain closed trace sourceError checked =>
      have same := SourceInternedRows.ViewError.invalidFTA.inj (Except.error.inj failed)
      subst error
      exact trace.builder_error state final value rows semantic covered available closed keys domain sourceError checked
  | returned final rows keys domain closed trace checked outcome work run => cases failed

/-- Every successful actual staged result has all exact bounded queries at the independent original root language. -/
theorem Execution.exact_queries (state final : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (result : Result) (api : Api)
    (actual : Execution given assumptions milliseconds check bound value state result final)
    (success : result = .ok (.ok (.ok api)))
    (model : FormulaLowering.Model ModelValue)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (SourceSizedLiquidAmbientAdequacy.truth
      (SourceSizedLiquidAmbient.Meaning model given assumptions)) ambient value term ∧ (nodeSize term : Int) ≤ bound) := by
  cases actual with
  | openRoot isOpen => cases success
  | invalid final rows keys domain closed trace error checked => cases success
  | returned final rows keys domain closed trace checked outcome work run =>
      cases outcome with
      | error failure => cases success
      | ok inner =>
          cases inner with
          | error unknown => cases success
          | ok output =>
              have same := Except.ok.inj (Except.ok.inj (Except.ok.inj success))
              subst api
              exact trace.liquid_exact state final value rows semantic covered guarded budgetHeap available closed keys domain
                checked model given assumptions milliseconds check correct bound output work run ambient

/-- Complete finite staged execution returns the exact error channel or a complete exact bounded query API. -/
theorem complete_exact (state : C) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : InternedOpenDepthReadback.Heap state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (completed : ∀ request, ∃ work attempt, check request work attempt)
    (model : FormulaLowering.Model ModelValue)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response) :
    ∃ result final, Execution given assumptions milliseconds check bound value state result final ∧
      ∀ api, result = .ok (.ok (.ok api)) → ∀ ambient,
        SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (SourceSizedLiquidAmbientAdequacy.truth
          (SourceSizedLiquidAmbient.Meaning model given assumptions)) ambient value term ∧ (nodeSize term : Int) ≤ bound) := by
  obtain ⟨result, final, actual⟩ := complete given assumptions milliseconds check bound value state semantic covered heap available completed
  exact ⟨result, final, actual, fun api success ambient =>
    actual.exact_queries given assumptions milliseconds check bound value state final semantic covered guarded budgetHeap available
      result api success model correct ambient⟩

/-- Actual closed repaired construction derives every internal premise of complete encoded public queries. -/
theorem constructed_complete (expression : InternedNestedConstruction.Syntax Symbol Guard) (state : C)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state)
    (completed : ∀ request, ∃ work attempt, check request work attempt) (model : FormulaLowering.Model ModelValue)
    (correct : ∀ request work response reached, check request work (.answered response reached) → ResponseCorrect model request response) :
    ∃ result final, Execution given assumptions milliseconds check bound value state result final ∧
      ∀ api, result = .ok (.ok (.ok api)) → ∀ ambient,
        SourceSizedApiLaws.Exact api (fun term => InternedGuardedLanguage.meaning (SourceSizedLiquidAmbientAdequacy.truth
          (SourceSizedLiquidAmbient.Meaning model given assumptions)) ambient value term ∧ (nodeSize term : Int) ≤ bound) := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value state built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have heap : InternedOpenDepthReadback.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  exact complete_exact given assumptions milliseconds check bound value state semantic covered heap guarded budgetHeap available completed model correct

end MicroCFTA.SourceFreshOrdinaryLiquidEntry
