import MicroCFTA.SourceCurrentConjunctionSharedWorklistTableSources
import MicroCFTA.SourceCurrentConjunctionRequirementRowsSemanticsStep

/-!
# Coupled semantic origins through successful shared execution

Each successful transition extends the same cell-origin and spine-source
lists. Actual sampling links table entries to these sources. Actual row
publication supplies the same descriptor batch and tail source. The finite
run derives every intermediate certificate from its current state. Failed
outcomes have no semantic assertion here. Terminal table coverage and the
Boolean answer remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistSemantics
open InternedConstructorTemplates (Value EdgeValue EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "TableInvariant" => SourceCurrentConjunctionSharedWorklistTableSources.Invariant
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual successful step extends its current coupled semantic certificate. -/
theorem step_sources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (p h : Nat) (before after : WorkState) (event : Event)
    (actual : step p h before = .done event after)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
    (origins : List Cell) (sources : List (List Tuple))
    (prior : TableInvariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
      origins sources before) :
    ∃ addedOrigins addedSources,
      TableInvariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        (origins ++ addedOrigins) (sources ++ addedSources) after := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact ⟨[], [], by simpa only [List.append_nil] using prior⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          have available : Values before.storage.requirements.physical.heap nodes :=
            values.pending nodes (by rw [pending]; exact List.mem_cons_self)
          rw [step_nodes p h before nodes rest pending] at actual
          obtain ⟨addedSources, kept⟩ := SourceCurrentConjunctionSharedWorklistTableSources.visit_sources
            formulas solver ambient h nodes rest before origins sources values.ready available prior
          rw [actual] at kept
          exact ⟨[], addedSources, by simpa only [List.append_nil, Outcome.state] using kept⟩
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              refine ⟨[], [], ?_⟩
              simp only [List.append_nil]
              exact ⟨prior.storage, prior.table⟩
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  have storage := SourceCurrentConjunctionRequirementRowsSemantics.force_success
                    forced values.ready values.cells closed.cells prior.storage
                  have current : TableInvariant
                      (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                      origins sources {before with storage := {before.storage with requirements := cells}} :=
                    ⟨storage, prior.table⟩
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have returned : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧
                      Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  obtain ⟨addedSources, kept⟩ := SourceCurrentConjunctionSharedWorklistTableSources.visit_sources
                    formulas solver ambient h nodes (.requirements handles :: rest)
                      {before with storage := {before.storage with requirements := cells}}
                      origins sources returned.1.ready returned.2.2 current
                  rw [actual] at kept
                  exact ⟨[], addedSources, by simpa only [List.append_nil, Outcome.state] using kept⟩
      | rows handle =>
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              obtain ⟨addedOrigins, addedSources, coupled⟩ :=
                SourceCurrentConjunctionRequirementRowsSemanticsStep.nextRow advanced values.ready
                  values.raw closed.raw prior.storage
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  exact ⟨addedOrigins, addedSources,
                    SourceCurrentConjunctionSharedWorklistTableSources.reframe prior
                      addedOrigins addedSources coupled rfl⟩
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  exact ⟨addedOrigins, addedSources,
                    SourceCurrentConjunctionSharedWorklistTableSources.reframe prior
                      addedOrigins addedSources coupled rfl⟩

/-- Actual successful finite runs derive their intermediate metadata without a future supplier. -/
theorem run_sources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    {p h : Nat} {before : WorkState} {outcome : Outcome Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome) :
    ∀ (origins : List Cell) (sources : List (List Tuple))
      (_values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
      (_closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
      (_prior : TableInvariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        origins sources before) (event : Event) (after : WorkState), outcome = .done event after →
        ∃ addedOrigins addedSources,
          TableInvariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
            (origins ++ addedOrigins) (sources ++ addedSources) after := by
  induction actual with
  | failed advanced =>
      intro origins sources values closed prior event after success
      cases success
  | @drained before after advanced =>
      intro origins sources values closed prior event final success
      cases success
      exact step_sources formulas solver ambient p h before after .drained advanced values closed origins sources prior
  | @more before middle outcome advanced tail ih =>
      intro origins sources values closed prior event after success
      obtain ⟨firstOrigins, firstSources, kept⟩ := step_sources formulas solver ambient p h before middle .more
        advanced values closed origins sources prior
      have middleValues : SourceCurrentConjunctionSharedWorklistValues.Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have middleClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant middle := by
        simpa only [advanced, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before values closed
      obtain ⟨lastOrigins, lastSources, final⟩ := ih (origins ++ firstOrigins) (sources ++ firstSources)
        middleValues middleClosed kept event after success
      exact ⟨firstOrigins ++ lastOrigins, firstSources ++ lastSources, by
        simpa only [List.append_assoc] using final⟩

/-- Original initialization derives coupled origins for every successful exploration and leaves faults explicit. -/
theorem explore_sources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (ambient : InternedGuardedLanguage.Env Symbol)
    (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    match SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before with
    | .failed _ _ => True
    | .done _ after => ∃ origins sources,
        TableInvariant (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
          origins sources after := by
  cases actual : SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before with
  | failed fault after => trivial
  | done event after =>
      obtain ⟨origins, sources, final⟩ := run_sources formulas solver ambient
        (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before) [] []
        (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
        (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before)
        (SourceCurrentConjunctionSharedWorklistTableSources.initial
          (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) budget start before)
        event after actual
      exact ⟨origins, sources, by simpa only [List.nil_append] using final⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistSemantics
