import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
import MicroCFTA.SourceCurrentConjunctionRequirementCellsProbes
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

/-!
# Clean probes through actual shared work

Actual sampling, cell forcing, and row preparation preserve the probe heap.
The finite run uses the value invariant at each reached state. Successful
and failed outcomes retain the probe predicate at the exact physical heap.
This result does not select a checked caller or supply execution bounds.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistProbes
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
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Each actual visit retains probes through skips, sampling, and every returned status. -/
theorem visit_probes (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) (ready : Ready before.storage.requirements.physical)
    (probes : ProbeHeap before.storage.requirements.physical.heap)
    (available : Values before.storage.requirements.physical.heap nodes) :
    ProbeHeap (visit h nodes rest before).state.storage.requirements.physical.heap := by
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact probes
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact probes
      | false =>
          have first := SourceCurrentConjunctionTuplePullTotalEffects.sample_probes h before.budget nodes
            before.storage.requirements.physical ready probes available
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state, withPhysical] using first
          | done result physical =>
              have clean : ProbeHeap physical.heap := by
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

/-- Every shared transition preserves probes at its exact successful or failed endpoint. -/
theorem step_probes (p h : Nat) (before : WorkState) (values : Invariant before)
    (probes : ProbeHeap before.storage.requirements.physical.heap) :
    ProbeHeap (step p h before).state.storage.requirements.physical.heap := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      exact probes
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          apply visit_probes h nodes rest before values.ready probes
          exact values.pending nodes (by rw [pending]; exact List.mem_cons_self)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              exact probes
          | cons handle handles =>
              have first := SourceCurrentConjunctionRequirementCellsProbes.force_probes p h handle
                before.storage.requirements values.ready probes values.cells
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state,
                    SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
              | done nodes cells =>
                  have clean : ProbeHeap cells.physical.heap := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using first
                  have own := SourceCurrentConjunctionRequirementCellsValues.force_values p h handle
                    before.storage.requirements values.ready values.cells
                  have current : Effects before.storage.requirements.physical cells.physical ∧
                      SourceCurrentConjunctionRequirementCellsValues.Invariant cells ∧ Values cells.physical.heap nodes := by
                    simpa only [forced, SourceCurrentConjunctionRequirementCells.Outcome.state] using own
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_probes h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    current.1.ready clean current.2.2
      | rows handle =>
          have first := SourceCurrentConjunctionRequirementRowsProbes.nextRow_probes handle before.storage probes
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state,
                SourceCurrentConjunctionSharedWorklistStep.Outcome.state] using first
          | done row storage =>
              have clean : ProbeHeap storage.requirements.physical.heap := by
                simpa only [advanced, SourceCurrentConjunctionRequirementRows.Outcome.state] using first
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact clean
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact clean

/-- The actual finite run derives probes at every terminal outcome from current inputs. -/
theorem run_probes {p h : Nat} {before : WorkState} {outcome : Outcome Symbol Formula}
    (actual : SourceCurrentConjunctionSharedWorklistRun.Run p h before outcome)
    (values : Invariant before) (probes : ProbeHeap before.storage.requirements.physical.heap) :
    ProbeHeap outcome.state.storage.requirements.physical.heap := by
  revert values probes
  induction actual with
  | @failed before after fault advanced =>
      intro values probes
      simpa only [advanced, Outcome.state] using step_probes p h before values probes
  | @drained before after advanced =>
      intro values probes
      simpa only [advanced, Outcome.state] using step_probes p h before values probes
  | @more before middle outcome advanced tail ih =>
      intro values probes
      have current : Invariant middle := by
        simpa only [advanced, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before values).2
      have clean : ProbeHeap middle.storage.requirements.physical.heap := by
        simpa only [advanced, Outcome.state] using step_probes p h before values probes
      exact ih current clean

/-- Original initialization derives probe preservation without a future trace or heap. -/
theorem explore_probes (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap start) :
    ProbeHeap (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap :=
  run_probes (SourceCurrentConjunctionSharedWorklistRun.explore_graph p h budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available) probes

end MicroCFTA.SourceCurrentConjunctionSharedWorklistProbes
