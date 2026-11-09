import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
import MicroCFTA.SourceCurrentConjunctionDemandMemos
import MicroCFTA.SourceCurrentConjunctionRequirementCellsMemos
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

/-!
# Ordered global receipts for successful shared work

Actual visits retain the complete sampling receipt. Actual requirement
forces retain their demanded projection order before the next visit. Row
preparation adds no global call. The same finite run threads each returned
memo bundle through its actual physical state. This module derives no
receipt for a terminal fault and makes no claim about failed reads.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistMemos
open Cache
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run explore explore_graph)
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
open SourceCurrentConjunctionDemandMemos (SampleReads)
open SourceCurrentConjunctionRequirementCellsMemos (ForceReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Task" => SourceCurrentConjunctionSharedWorklistStep.Task Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Closed" => SourceCurrentConjunctionSharedWorklistClosed.Invariant
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A successful visit records only its selected skip or actual sampling branch. -/
inductive VisitReads : {h : Nat} → {nodes : List Node} → {rest : List Task} →
    {before after : WorkState} → {event : Event} →
    (visit h nodes rest before = .done event after) → Memos → Memos → Prop where
  | empty {h : Nat} {nodes : List Node} {rest : List Task} {before after : WorkState} {event : Event}
      {actual : visit h nodes rest before = .done event after} {memos : Memos}
      (empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = true) : VisitReads actual memos memos
  | skip {h : Nat} {nodes : List Node} {rest : List Task} {before after : WorkState} {event : Event}
      {actual : visit h nodes rest before = .done event after} {memos : Memos}
      (nonempty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = false)
      (skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget
        (queryTable before.table) nodes = true) : VisitReads actual memos memos
  | sample {h : Nat} {nodes : List Node} {rest : List Task} {before after : WorkState} {event : Event}
      {actual : visit h nodes rest before = .done event after} {memos saved : Memos}
      {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula} {physical : Physical}
      {sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
        before.storage.requirements.physical = .done result physical}
      (nonempty : nodes.any SourceCurrentConjunctionRequirements.isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget
        (queryTable before.table) nodes = false)
      (calls : SampleReads sampled memos saved) : VisitReads actual memos saved

/-- One transition orders actual force calls before its actual visit calls. -/
inductive StepReads : {p h : Nat} → {before after : WorkState} → {event : Event} →
    (step p h before = .done event after) → Memos → Memos → Prop where
  | drained {p h : Nat} {before after : WorkState} {event : Event}
      {actual : step p h before = .done event after} {memos : Memos}
      (pending : before.pending = []) : StepReads actual memos memos
  | nodes {p h : Nat} {before after : WorkState} {event : Event}
      {actual : step p h before = .done event after} {memos saved : Memos}
      {nodes : List Node} {rest : List Task}
      (pending : before.pending = .nodes nodes :: rest)
      (visited : visit h nodes rest before = .done event after)
      (calls : VisitReads visited memos saved) : StepReads actual memos saved
  | requirements_nil {p h : Nat} {before after : WorkState} {event : Event}
      {actual : step p h before = .done event after} {memos : Memos} {rest : List Task}
      (pending : before.pending = .requirements [] :: rest) : StepReads actual memos memos
  | requirement {p h : Nat} {before after : WorkState} {event : Event}
      {actual : step p h before = .done event after} {memos middle saved : Memos}
      {handle : Nat} {handles : List Nat} {rest : List Task} {nodes : List Node}
      {cells : SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula}
      (pending : before.pending = .requirements (handle :: handles) :: rest)
      {forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements = .done nodes cells}
      (first : ForceReads forced memos middle)
      (visited : visit h nodes (.requirements handles :: rest)
        {before with storage := {before.storage with requirements := cells}} = .done event after)
      (last : VisitReads visited middle saved) : StepReads actual memos saved
  | rows {p h : Nat} {before after : WorkState} {event : Event}
      {actual : step p h before = .done event after} {memos : Memos} {handle : Nat} {rest : List Task}
      {row : Option (List Nat × Nat)} {storage : SourceCurrentConjunctionRequirementRows.State Symbol FullSyntax.Formula}
      (pending : before.pending = .rows handle :: rest)
      (advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .done row storage) :
      StepReads actual memos memos

/-- A successful finite graph sequences each actual transition receipt without reordering it. -/
inductive RunReads : {p h : Nat} → {before : WorkState} → {outcome : Outcome Symbol FullSyntax.Formula} →
    Run p h before outcome → Memos → Memos → Prop where
  | drained (calls : StepReads actual memos saved) : RunReads (.drained actual) memos saved
  | more (first : StepReads actual memos middle) (rest : RunReads tail middle saved) :
      RunReads (.more actual tail) memos saved

/-- The successful literal exploration is paired with its own derived finite graph. -/
def ExploreReads {p h budget : Nat} {start : Node} {before : Physical} {event : Event} {after : WorkState}
    (_actual : explore p h budget start before = .done event after) (memos saved : Memos) : Prop :=
  ∃ actual : Run p h (initial budget start before) (.done event after), RunReads actual memos saved

/-- Every successful visit derives sampling receipts and the exact returned coherent bundle. -/
theorem visit_memos {h : Nat} {nodes : List Node} {rest : List Task} {before after : WorkState} {event : Event}
    (actual : visit h nodes rest before = .done event after)
    (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes) (memos : Memos)
    (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, VisitReads actual memos saved ∧ Valid after.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty] at actual
      cases actual
      exact ⟨memos, .empty empty, valid, extends_refl _, rfl⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped] at actual
          cases actual
          exact ⟨memos, .skip empty skipped, valid, extends_refl _, rfl⟩
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled] at actual
              cases actual
          | done result physical =>
              obtain ⟨saved, calls, coherent, retained, same⟩ := SourceCurrentConjunctionDemandMemos.sample_memos
                sampled ready.semantic ready.costs available memos valid
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled] at actual
                  cases actual
                  exact ⟨saved, .sample empty skipped calls, coherent, retained, same⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled] at actual
                      cases actual
                      exact ⟨saved, .sample empty skipped calls, coherent, retained, same⟩
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled] at actual
                      cases actual
                      exact ⟨saved, .sample empty skipped calls, coherent, retained, same⟩

/-- Every successful transition derives force and sample calls in its literal selected order. -/
theorem step_memos {p h : Nat} {before after : WorkState} {event : Event}
    (actual : step p h before = .done event after) (values : Invariant before) (closedInputs : Closed before)
    (memos : Memos) (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, StepReads actual memos saved ∧ Valid after.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact ⟨memos, .drained pending, valid, extends_refl _, rfl⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          have visited := (step_nodes p h before nodes rest pending).symm.trans actual
          obtain ⟨saved, calls, coherent, retained, same⟩ := visit_memos visited values.ready
            (values.pending nodes (by rw [pending]; exact List.mem_cons_self)) memos valid
          exact ⟨saved, .nodes pending visited calls, coherent, retained, same⟩
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              exact ⟨memos, .requirements_nil pending, valid, extends_refl _, rfl⟩
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  obtain ⟨middle, first, coherent, retained, same⟩ := SourceCurrentConjunctionRequirementCellsMemos.force_memos
                    forced values.ready values.cells closedInputs.cells memos valid
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  have visited := (step_requirement_done p h handle handles before rest nodes cells pending forced).symm.trans actual
                  obtain ⟨saved, last, finalValid, finalRetained, finalSame⟩ :=
                    visit_memos visited current.1.ready current.2.2 middle coherent
                  exact ⟨saved, .requirement pending first visited last, finalValid,
                    extends_trans retained finalRetained, finalSame.trans same⟩
      | rows handle =>
          have preserved := SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap handle before.storage
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              have sameHeap : storage.requirements.physical.heap = before.storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using preserved
              have coherent : Valid storage.requirements.physical.heap memos := by
                rw [sameHeap]
                exact valid
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  exact ⟨memos, .rows pending advanced, coherent, extends_refl _, rfl⟩
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  exact ⟨memos, .rows pending advanced, coherent, extends_refl _, rfl⟩

private theorem run_outcome_memos {p h : Nat} {before : WorkState} {outcome : Outcome Symbol FullSyntax.Formula}
    (actual : Run p h before outcome) (values : Invariant before) (closedInputs : Closed before)
    (memos : Memos) (valid : Valid before.storage.requirements.physical.heap memos) :
    match outcome with
    | .failed _ _ => True
    | .done _ after => ∃ saved, RunReads actual memos saved ∧ Valid after.storage.requirements.physical.heap saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  revert values closedInputs memos valid
  induction actual with
  | failed advanced => intro values closedInputs memos valid; trivial
  | drained advanced =>
      intro values closedInputs memos valid
      obtain ⟨saved, calls, coherent, retained, same⟩ := step_memos advanced values closedInputs memos valid
      exact ⟨saved, .drained calls, coherent, retained, same⟩
  | @more before middle outcome advanced tail ih =>
      intro values closedInputs memos valid
      obtain ⟨middleMemo, first, coherent, retained, same⟩ := step_memos advanced values closedInputs memos valid
      have current : Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have currentClosed : Closed middle := by
        simpa only [advanced, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before values closedInputs
      have rest := ih current currentClosed middleMemo coherent
      cases outcome with
      | failed fault after => trivial
      | done event after =>
          obtain ⟨saved, last, finalValid, finalRetained, finalSame⟩ := rest
          exact ⟨saved, .more first last, finalValid, extends_trans retained finalRetained, finalSame.trans same⟩

/-- A successful actual finite run derives its own ordered coherent global receipts. -/
theorem run_memos {p h : Nat} {before after : WorkState} {event : Event}
    (actual : Run p h before (.done event after)) (values : Invariant before) (closedInputs : Closed before)
    (memos : Memos) (valid : Valid before.storage.requirements.physical.heap memos) :
    ∃ saved, RunReads actual memos saved ∧ Valid after.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query :=
  run_outcome_memos actual values closedInputs memos valid

/-- Original current facts derive receipts for the same successful literal exploration. -/
theorem explore_memos {p h budget : Nat} {start : Node} {before : Physical} {event : Event} {after : WorkState}
    (ready : Ready before) (available : Available before.heap start) (memos : Memos) (valid : Valid before.heap memos)
    (actual : explore p h budget start before = .done event after) :
    ∃ saved, ExploreReads actual memos saved ∧ Valid after.storage.requirements.physical.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  have graph : Run p h (initial budget start before) (.done event after) := by
    rw [← actual]
    exact explore_graph p h budget start before
  obtain ⟨saved, calls, coherent, retained, same⟩ := run_memos graph
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
    (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before) memos valid
  exact ⟨saved, ⟨graph, calls⟩, coherent, retained, same⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistMemos
