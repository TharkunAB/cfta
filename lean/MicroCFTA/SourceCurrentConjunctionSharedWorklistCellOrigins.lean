import MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement
import MicroCFTA.SourceCurrentConjunctionRequirementRowsOriginWitness
import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed

/-!
# Original descriptors through successful shared execution

Initialization supplies no origins. Actual row allocation appends literal
descriptor batches. Successful forcing preserves their common-term claims
at the same handles. The finite execution graph derives every intermediate
origin list. Failed forcing has no semantic refinement assertion here.
Row-spine provenance and semantic table coverage remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistCellOrigins
open InternedConstructorTemplates (Value EdgeValue EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "Refined" => SourceCurrentConjunctionRequirementCellsRefinement.Invariant

/-- Each batch contains a raw tuple and classes for literal descriptors. -/
structure Batch (Symbol Formula : Type) where
  tuple : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))
  constraints : EqualityNormalize.Constraints

/-- The origin list retains the literal descriptor order within each batch. -/
def flatten (batches : List (Batch Symbol Formula)) : List Cell :=
  batches.flatMap fun batch => SourceCurrentConjunctionRequirementRows.descriptors batch.tuple batch.constraints

private theorem same_cells {before after : Cells} {origins : List Cell}
    (refined : Refined origins before) (same : after.cells = before.cells) : Refined origins after := by
  refine ⟨refined.length.trans (congrArg List.length same).symm, ?_⟩
  intro handle original current originFound currentFound
  apply refined.cells handle original current originFound
  simpa only [SourceCurrentConjunctionRequirementCells.lookup, same] using currentFound

/-- Actual initialization derives the empty origin list. -/
theorem initial_origins (budget : Nat) (start : Node) (before : Physical) :
    Refined [] (initial budget start before).storage.requirements :=
  SourceCurrentConjunctionRequirementCellsRefinement.initial before

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_cells (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) :
    (visit h nodes rest before).state.storage.requirements.cells = before.storage.requirements.cells := by
  unfold visit
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- Native sampling and row-spine allocation preserve all existing origin claims. -/
theorem visit_origins (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (origins : List Cell) (refined : Refined origins before.storage.requirements) :
    Refined origins (visit h nodes rest before).state.storage.requirements :=
  same_cells refined (visit_cells h nodes rest before)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem nextRow_origins (handle : Nat)
    (before : SourceCurrentConjunctionRequirementRows.State Symbol Formula) (origins : List Cell)
    (refined : Refined origins before.requirements) :
    ∃ batches, Refined (origins ++ flatten batches)
      (SourceCurrentConjunctionRequirementRows.nextRow handle before).state.requirements := by
  obtain ⟨added, kept, _, shape⟩ :=
    SourceCurrentConjunctionRequirementRowsRefinement.nextRow_refinement handle before origins refined
  rcases shape with empty | ⟨tuple, constraints, same⟩
  · subst added
    exact ⟨[], by simpa only [flatten, List.flatMap_nil, List.append_nil] using kept⟩
  · subst added
    exact ⟨[⟨tuple, constraints⟩], by
      simpa only [flatten, List.flatMap_cons, List.flatMap_nil, List.append_nil] using kept⟩

/-- An actual successful step derives its appended descriptor batches from current storage. -/
theorem step_origins (p h : Nat) (before after : WorkState) (event : Event)
    (actual : step p h before = .done event after)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
    (origins : List Cell) (refined : Refined origins before.storage.requirements) :
    ∃ batches, Refined (origins ++ flatten batches) after.storage.requirements := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact ⟨[], by simpa only [flatten, List.flatMap_nil, List.append_nil] using refined⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at actual
          have kept := visit_origins h nodes rest before origins refined
          rw [actual] at kept
          exact ⟨[], by simpa only [flatten, List.flatMap_nil, List.append_nil, Outcome.state] using kept⟩
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              exact ⟨[], by simpa only [flatten, List.flatMap_nil, List.append_nil] using refined⟩
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  have first := SourceCurrentConjunctionRequirementCellsRefinement.force_success
                    forced values.ready values.cells closed.cells refined
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  have kept := visit_origins h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} origins first
                  rw [actual] at kept
                  exact ⟨[], by simpa only [flatten, List.flatMap_nil, List.append_nil, Outcome.state] using kept⟩
      | rows handle =>
          obtain ⟨batches, kept⟩ := nextRow_origins handle before.storage origins refined
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              rw [advanced] at kept
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  exact ⟨batches, kept⟩
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  exact ⟨batches, kept⟩

/-- A successful actual finite graph derives every origin extension without a future supplier. -/
theorem run_origins {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome) :
    ∀ (origins : List Cell) (_values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
      (_closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
      (_refined : Refined origins before.storage.requirements) (event : Event) (after : WorkState),
      outcome = .done event after →
        ∃ batches, Refined (origins ++ flatten batches) after.storage.requirements := by
  induction actual with
  | failed advanced =>
      intro origins values closed refined event after success
      cases success
  | @drained before after advanced =>
      intro origins values closed refined event final success
      cases success
      exact step_origins p h before after .drained advanced values closed origins refined
  | @more before middle outcome advanced tail ih =>
      intro origins values closed refined event after success
      obtain ⟨first, kept⟩ := step_origins p h before middle .more advanced values closed origins refined
      have middleValues : SourceCurrentConjunctionSharedWorklistValues.Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have middleClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant middle := by
        simpa only [advanced, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before values closed
      obtain ⟨last, final⟩ := ih (origins ++ flatten first) middleValues middleClosed kept event after success
      exact ⟨first ++ last, by simpa only [flatten, List.flatMap_append, List.append_assoc] using final⟩

/-- An exact registered witness survives an actual successful suffix into its cached final cell. -/
theorem run_stored_witness {p h : Nat} {event : Event} {before after : WorkState}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before (.done event after))
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
    (origins : List Cell) (refined : Refined origins before.storage.requirements)
    (handle : Nat) (original : Cell) (nodes : List Node)
    (originFound : origins[handle]? = some original)
    (currentDone : SourceCurrentConjunctionRequirementCells.lookup handle after.storage.requirements = some (.done nodes))
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Language.Term Symbol)) (part : Language.Term Symbol)
    (common : SourceCurrentConjunctionRequirementCellsSoundness.CommonCell holds ambient symbol terms part original) :
    SourceCurrentConjunctionEmptinessRows.Accepts (InternedGuardedLanguage.meaning holds ambient) nodes part := by
  obtain ⟨batches, kept⟩ := run_origins actual origins values closed refined event after rfl
  have extended : (origins ++ flatten batches)[handle]? = some original := by
    rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp originFound).1)]
    exact originFound
  exact SourceCurrentConjunctionRequirementRowsOriginWitness.stored_done_witness
    (origins ++ flatten batches) after.storage.requirements handle original nodes kept extended currentDone
    holds ambient symbol terms part common

/-- Original inputs derive origin refinement for every successful exploration; faults remain explicit. -/
theorem explore_origins (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    match SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before with
    | .failed _ _ => True
    | .done _ after => ∃ batches, Refined (flatten batches) after.storage.requirements := by
  cases actual : SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before with
  | failed fault after => trivial
  | done event after =>
      obtain ⟨batches, kept⟩ := run_origins
        (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before) []
        (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
        (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before)
        (initial_origins budget start before) event after actual
      exact ⟨batches, by simpa only [List.nil_append] using kept⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistCellOrigins
