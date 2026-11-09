import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
import MicroCFTA.SourceCurrentConjunctionRequirementCellsAnnotations
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes
import MicroCFTA.SourceCurrentConjunctionDemandAnnotations

/-!
# Physical annotations through actual shared work

Actual sampling, cell forcing, and row preparation preserve each physical
annotation predicate. The finite run derives current resident and closed
stored operands at each reached state. Success and failure retain the
predicate at the exact returned heap. Initialization needs no closed query.
This result does not select a checked caller or supply execution bounds.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistAnnotations
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Each actual visit retains physical annotations on every returned status. -/
theorem visit_heap (annotation : Guard → Prop) (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (ready : Ready before.storage.requirements.physical)
    (known : AnnotationHeap annotation before.storage.requirements.physical.heap)
    (available : Values before.storage.requirements.physical.heap nodes) :
    AnnotationHeap annotation (visit h nodes rest before).state.storage.requirements.physical.heap := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact known
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact known
      | false =>
          have first := SourceCurrentConjunctionDemandAnnotations.sample_annotation_heap annotation h before.budget nodes
            before.storage.requirements.physical ready.semantic ready.costs available known
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state, withPhysical] using first
          | done result physical =>
              have clean : AnnotationHeap annotation physical.heap := by
                simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact clean
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact clean
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      exact clean

/-- Every shared transition retains annotations at its exact returned heap. -/
theorem step_heap (annotation : Guard → Prop) (p h : Nat) (before : WorkState)
    (values : Invariant before) (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
    (known : AnnotationHeap annotation before.storage.requirements.physical.heap) :
    AnnotationHeap annotation (step p h before).state.storage.requirements.physical.heap := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact known
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_heap annotation h nodes rest before values.ready known
          exact values.pending nodes (by rw [pending]; exact List.mem_cons_self)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact known
          | cons handle handles =>
              have first := SourceCurrentConjunctionRequirementCellsAnnotations.force_heap annotation p h handle
                before.storage.requirements values.ready values.cells closed.cells known
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state,
                    SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
              | done nodes cells =>
                  have clean : AnnotationHeap annotation cells.physical.heap := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using first
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_heap annotation h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    current.1.ready clean current.2.2
      | rows handle =>
          have first : AnnotationHeap annotation
              (SourceCurrentConjunctionRequirementRows.nextRow handle before.storage).state.requirements.physical.heap := by
            rw [SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap]
            exact known
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
          | done row storage =>
              have clean : AnnotationHeap annotation storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact clean
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact clean

/-- The actual finite run derives annotations at every terminal outcome. -/
theorem run_heap (annotation : Guard → Prop) {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (values : Invariant before) (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before)
    (known : AnnotationHeap annotation before.storage.requirements.physical.heap) :
    AnnotationHeap annotation outcome.state.storage.requirements.physical.heap := by
  revert values closed known
  induction actual with
  | @failed before after fault advanced =>
      intro values closed known
      simpa only [advanced, Outcome.state] using step_heap annotation p h before values closed known
  | @drained before after advanced =>
      intro values closed known
      simpa only [advanced, Outcome.state] using step_heap annotation p h before values closed known
  | @more before middle outcome advanced tail ih =>
      intro values closed known
      have current : Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have clean : AnnotationHeap annotation middle.storage.requirements.physical.heap := by
        simpa only [advanced, Outcome.state] using step_heap annotation p h before values closed known
      have nextClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant middle := by
        simpa only [advanced, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before values closed
      exact ih current nextClosed clean

/-- Original initialization derives annotation preservation without a closed query premise. -/
theorem explore_heap (annotation : Guard → Prop) (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : AnnotationHeap annotation before.heap) (available : Available before.heap start) :
    AnnotationHeap annotation (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap :=
  run_heap annotation (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
    (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before) known

end MicroCFTA.SourceCurrentConjunctionSharedWorklistAnnotations
