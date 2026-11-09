import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
import MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample

/-!
# Closed stored values through actual shared exploration

Stored cells, pending raw tuples, and table queries are closed. Pending node
tasks may remain open. An actual admitted visit derives closed operands from
the source skip test before it samples them. Initialization needs no closed
query premise. The actual finite graph supplies every intermediate state.
The selected caller and Boolean soundness remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
open InternedConstructorTemplates (Value EdgeKey EdgeValue)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed

/-- Actual stored operands are closed without a requirement on pending node tasks. -/
structure Invariant (before : WorkState) : Prop where
  cells : SourceCurrentConjunctionRequirementCellsClosed.Invariant before.storage.requirements
  raw : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed before.storage
  table : ∀ entry ∈ before.table, ClosedValues entry.nodes

private theorem allocate_raw (tuples : List (List Row)) (before : Storage)
    (prior : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed before)
    (added : ∀ tuple ∈ tuples, ClosedEdges tuple) :
    SourceCurrentConjunctionRequirementRowsClosed.SpineClosed
      (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending tuples) before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact prior spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp fresh
    cases same
    exact added

/-- Original initialization has no stored closure obligation, even for an open query. -/
theorem initial_closed (budget : Nat) (start : Node) (before : Physical) :
    Invariant (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  refine ⟨SourceCurrentConjunctionRequirementCellsClosed.initial_closed before, ?_, ?_⟩
  · intro spine member
    cases member
  · intro entry member
    cases member

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit derives closed sampled tuples and retains all stored closure facts. -/
theorem visit_closed (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes) (prior : Invariant before) :
    Invariant (visit h nodes rest before).state := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨prior.cells, prior.raw, prior.table⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget
          (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨prior.cells, prior.raw, prior.table⟩
      | false =>
          have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed before.budget
            (queryTable before.table) nodes skipped
          have queryClosed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              exact ⟨prior.cells, prior.raw, prior.table⟩
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨prior.cells, prior.raw, prior.table⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      refine ⟨prior.cells, prior.raw, ?_⟩
                      intro entry member
                      rcases List.mem_cons.mp member with same | old
                      · cases same
                        exact queryClosed
                      · exact prior.table entry old
                  | cons tuple tuples =>
                      have tuplesClosed := SourceCurrentConjunctionTuplePullClosedSample.sample_fit
                        h before.budget nodes before.storage.requirements.physical physical (tuple :: tuples)
                        sampled ready available queryClosed
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨prior.cells, ?_, ?_⟩
                      · exact allocate_raw (tuple :: tuples) (withPhysical before physical).storage
                          prior.raw tuplesClosed
                      · intro entry member
                        rcases List.mem_cons.mp member with same | old
                        · cases same
                          exact queryClosed
                        · exact prior.table entry old

/-- Every actual task outcome derives stored closedness from current resident operands. -/
theorem step_closed (p h : Nat) (before : WorkState)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before) (prior : Invariant before) :
    Invariant (step p h before).state := by
  cases pending : before.pending with
  | nil => rw [step_nil p h before pending]; exact prior
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_closed h nodes rest before values.ready _ prior
          apply values.pending nodes
          rw [pending]
          exact List.mem_cons_self
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact ⟨prior.cells, prior.raw, prior.table⟩
          | cons handle handles =>
              have forcedValues := SourceCurrentConjunctionRequirementCellsValues.force_values
                p h handle before.storage.requirements values.ready values.cells
              have forcedClosed := SourceCurrentConjunctionRequirementCellsClosed.force_closed
                p h handle before.storage.requirements values.ready values.cells prior.cells
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  have cellsClosed : SourceCurrentConjunctionRequirementCellsClosed.Invariant cells := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using forcedClosed.1
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  exact ⟨cellsClosed, prior.raw, prior.table⟩
              | done nodes cells =>
                  have current : SourceCurrentConjunctionRowsAllocation.Effects
                      before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧
                      Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using forcedValues
                  have cellsClosed : SourceCurrentConjunctionRequirementCellsClosed.Invariant cells := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using forcedClosed.1
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_closed h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    current.1.ready current.2.2 ⟨cellsClosed, prior.raw, prior.table⟩
      | rows handle =>
          have advancedClosed := SourceCurrentConjunctionRequirementRowsClosed.nextRow_closed
            handle before.storage prior.cells prior.raw
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [advanced] at advancedClosed
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨advancedClosed.1, advancedClosed.2, prior.table⟩
          | done row storage =>
              rw [advanced] at advancedClosed
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨advancedClosed.1, advancedClosed.2, prior.table⟩
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact ⟨advancedClosed.1, advancedClosed.2, prior.table⟩

/-- The actual finite graph derives all intermediate closure and residency certificates. -/
theorem run_closed {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before) (prior : Invariant before) :
    Invariant outcome.state := by
  revert values prior
  induction actual with
  | @failed before after fault observed =>
      intro values prior
      simpa only [observed, Outcome.state] using step_closed p h before values prior
  | @drained before after observed =>
      intro values prior
      simpa only [observed, Outcome.state] using step_closed p h before values prior
  | @more before middle outcome observed tail ih =>
      intro values prior
      have nextValues : SourceCurrentConjunctionSharedWorklistValues.Invariant middle := by
        simpa only [observed, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have nextClosed : Invariant middle := by
        simpa only [observed, Outcome.state] using step_closed p h before values prior
      exact ih nextValues nextClosed

/-- Any available original query derives stored closedness on success and failure. -/
theorem explore_closed (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    Invariant (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state :=
  run_closed (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
    (initial_closed budget start before)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
