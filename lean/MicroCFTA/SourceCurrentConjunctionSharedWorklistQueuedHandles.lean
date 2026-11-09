import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
import MicroCFTA.SourceCurrentConjunctionSharedWorklistHandleValidity
import MicroCFTA.SourceCurrentConjunctionRequirementPublication

/-!
# Present requirement handles in actual shared queues

Every queued requirement handle is within the current private cell heap.
Actual row publication supplies new queued handles. Sampling retains cell
counts, row preparation can append cells, and forcing retains their count.
Initialization and the actual finite run derive the invariant on success
and failure. This result does not require native readiness or execution
bounds, and it does not assert that a stored cell must be queued.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistQueuedHandles
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistHandleValidity (Valid RowCells)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula

/-- Every handle in every queued requirement task has an allocated cell. -/
def QueuedHandles (before : WorkState) : Prop :=
  ∀ handles, Task.requirements handles ∈ before.pending →
    ∀ handle ∈ handles, handle < before.storage.requirements.cells.length

/-- Current cached-row validity and queued-handle validity use the same private heaps. -/
structure Invariant (before : WorkState) : Prop where
  stored : Valid before
  queued : QueuedHandles before

/-- An actual successful row observation derives all returned handles from its own publication. -/
theorem nextRow_handles (target : Nat) (before after : Storage) (handles : List Nat) (tail : Nat)
    (valid : RowCells before)
    (actual : SourceCurrentConjunctionRequirementRows.nextRow target before = .done (some (handles, tail)) after) :
    ∀ handle ∈ handles, handle < after.requirements.cells.length := by
  have current := SourceCurrentConjunctionSharedWorklistHandleValidity.nextRow_valid target before valid
  rw [actual] at current
  have published := SourceCurrentConjunctionRequirementPublication.nextRow_done target before after
    (some (handles, tail)) actual
  exact current (.done (some (handles, tail))) (List.mem_of_getElem? published)

/-- Original initialization has no queued requirement handle. -/
theorem initial (budget : Nat) (start : Node) (before : Physical) :
    Invariant (SourceCurrentConjunctionSharedWorklistStep.initial budget start before) := by
  refine ⟨SourceCurrentConjunctionSharedWorklistHandleValidity.initial budget start before, ?_⟩
  intro handles member
  have impossible := List.mem_singleton.mp member
  cases impossible

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_queued (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState)
    (prior : ∀ handles, Task.requirements handles ∈ rest →
      ∀ handle ∈ handles, handle < before.storage.requirements.cells.length) :
    QueuedHandles (visit h nodes rest before).state := by
  unfold visit
  split
  · exact prior
  · split
    · exact prior
    · cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
          before.storage.requirements.physical with
      | failed fault physical =>
          intro handles member
          rcases List.mem_cons.mp member with impossible | old
          · cases impossible
          · exact prior handles old
      | done result physical =>
          cases result with
          | overflow tuples cursor => exact prior
          | fit tuples =>
              cases tuples with
              | nil => exact prior
              | cons tuple tuples =>
                  intro handles member
                  rcases List.mem_cons.mp member with impossible | old
                  · cases impossible
                  · exact prior handles old

/-- Every actual visit retains queued handles and derives its new cached-row validity. -/
theorem visit_preserves (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (prior : Invariant {before with pending := .nodes nodes :: rest}) :
    Invariant (visit h nodes rest before).state := by
  refine ⟨SourceCurrentConjunctionSharedWorklistHandleValidity.visit_valid h nodes rest before
    ⟨prior.stored.rows, prior.stored.table⟩, ?_⟩
  exact visit_queued h nodes rest before
    (fun handles member => prior.queued handles (List.mem_cons_of_mem _ member))

/-- Every actual task outcome retains all queued requirement handles in the actual cell heap. -/
theorem step_preserves (p h : Nat) (before : WorkState) (prior : Invariant before) :
    Invariant (step p h before).state := by
  refine ⟨SourceCurrentConjunctionSharedWorklistHandleValidity.step_valid p h before prior.stored, ?_⟩
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact prior.queued
  | cons task rest =>
      have remaining : ∀ handles, Task.requirements handles ∈ rest →
          ∀ handle ∈ handles, handle < before.storage.requirements.cells.length := by
        intro handles member
        apply prior.queued handles
        rw [pending]
        exact List.mem_cons_of_mem _ member
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_queued h nodes rest before remaining
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact remaining
          | cons handle handles =>
              have length := SourceCurrentConjunctionRequirementCellsFrame.force_length p h handle before.storage.requirements
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [forced] at length
                  change cells.cells.length = before.storage.requirements.cells.length at length
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  intro query member target included
                  change target < cells.cells.length
                  rw [length]
                  exact prior.queued query member target included
              | done nodes cells =>
                  rw [forced] at length
                  change cells.cells.length = before.storage.requirements.cells.length at length
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  apply visit_queued h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                  intro query member target included
                  change target < cells.cells.length
                  rw [length]
                  rcases List.mem_cons.mp member with same | old
                  · have equal : query = handles := Task.requirements.inj same
                    subst query
                    apply prior.queued (handle :: handles) _ target (List.mem_cons_of_mem _ included)
                    rw [pending]
                    exact List.mem_cons_self
                  · exact remaining query old target included
      | rows target =>
          have grown := SourceCurrentConjunctionRequirementRowsFrame.nextRow_cells_le target before.storage
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow target before.storage with
          | failed fault storage =>
              rw [advanced] at grown
              rw [step_rows_failed p h target before rest fault storage pending advanced]
              intro handles member handle included
              exact Nat.lt_of_lt_of_le (prior.queued handles member handle included) grown
          | done row storage =>
              rw [advanced] at grown
              cases row with
              | none =>
                  rw [step_rows_none p h target before rest storage pending advanced]
                  intro handles member handle included
                  exact Nat.lt_of_lt_of_le (remaining handles member handle included) grown
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  have own := nextRow_handles target before.storage storage handles tail prior.stored.rows advanced
                  rw [step_rows_live p h target tail before rest handles storage pending advanced]
                  intro query member handle included
                  rcases List.mem_cons.mp member with same | member
                  · have equal : query = handles := Task.requirements.inj same
                    subst query
                    exact own handle included
                  · rcases List.mem_cons.mp member with impossible | old
                    · cases impossible
                    · exact Nat.lt_of_lt_of_le (remaining query old handle included) grown

/-- The actual finite run derives queued-handle validity at its exact terminal outcome. -/
theorem run_preserves {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome) (prior : Invariant before) :
    Invariant outcome.state := by
  revert prior
  induction actual with
  | @failed before after fault advanced =>
      intro prior
      simpa only [advanced, Outcome.state] using step_preserves p h before prior
  | @drained before after advanced =>
      intro prior
      simpa only [advanced, Outcome.state] using step_preserves p h before prior
  | @more before middle outcome advanced tail ih =>
      intro prior
      apply ih
      simpa only [advanced, Outcome.state] using step_preserves p h before prior

/-- Original exploration derives valid queued and cached handles without a future-state premise. -/
theorem explore_handles (p h budget : Nat) (start : Node) (before : Physical) :
    Invariant (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state :=
  run_preserves (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (initial budget start before)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistQueuedHandles
