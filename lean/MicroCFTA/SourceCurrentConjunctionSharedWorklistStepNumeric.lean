import MicroCFTA.SourceCurrentConjunctionSharedWorklistCompletion
import MicroCFTA.SourceCurrentConjunctionRequirementCellsNumeric
import MicroCFTA.SourceCurrentConjunctionRequirementCellsOutputBounds
import MicroCFTA.SourceCurrentConjunctionTuplePullNumeric
import MicroCFTA.SourceCurrentConjunctionRequirementRowsProbes

/-!
# Computed bounds for one actual shared worklist transition

The current task and its stored cell determine the scalar schedule and
both observation bounds. Admission derives closed sampling operands from
the actual skip test. Open queued queries need no closedness premise.
The proof returns the same full state at every sufficient computed bound.
This local schedule does not bound a complete worklist or native capacity.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumeric
open InternedConstructorTemplates (Value EdgeKey)
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- The current task bounds native heap growth through forcing and sampling. -/
def forecast (before : WorkState) (resource : Nat) : Nat :=
  match before.pending with
  | .nodes nodes :: _ => SourceCurrentConjunctionExposureResources.forecast nodes.length resource
  | .requirements (handle :: _) :: _ =>
      let cells := before.storage.requirements
      let next := SourceCurrentConjunctionRequirementCellsNumeric.forecast handle cells resource
      let count := SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle cells
      SourceCurrentConjunctionExposureResources.forecast count next
  | _ => resource

/-- Only a pending requirement can need a projection worker. -/
def projectionFuel (before : WorkState) : Nat :=
  match before.pending with
  | .requirements (handle :: _) :: _ =>
      SourceCurrentConjunctionRequirementCellsNumeric.projectionFuel handle before.storage.requirements
  | _ => 0

/-- Forcing and its following sample share the maximum of their computed read bounds. -/
def readerFuel (before : WorkState) (resource : Nat) : Nat :=
  match before.pending with
  | .nodes nodes :: _ => SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length resource
  | .requirements (handle :: _) :: _ =>
      let cells := before.storage.requirements
      let next := SourceCurrentConjunctionRequirementCellsNumeric.forecast handle cells resource
      let count := SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle cells
      max (SourceCurrentConjunctionRequirementCellsNumeric.readerFuel handle cells resource)
        (SourceCurrentConjunctionTuplePullNumeric.fuel count next)
  | _ => 0

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Current available operands derive the complete visit at its computed sampling bound. -/
theorem visit_complete (nodes : List Node) (rest : List (Task Symbol Formula)) (before : WorkState)
    (resource : Nat) (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes)
    (fits : Fits resource before.storage.requirements.physical.heap) :
    ∃ event after,
      (∀ h, SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length resource ≤ h →
        visit h nodes rest before = .done event after) ∧
      Fits (SourceCurrentConjunctionExposureResources.forecast nodes.length resource)
        after.storage.requirements.physical.heap := by
  cases empty : nodes.any isEmpty with
  | true =>
      exact ⟨.more, _, fun h _ => visit_empty h nodes rest before empty,
        fits.mono (SourceCurrentConjunctionExposureResources.forecast_ge _ _)⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true =>
          exact ⟨.more, _, fun h _ => visit_skip h nodes rest before empty skipped,
            fits.mono (SourceCurrentConjunctionExposureResources.forecast_ge _ _)⟩
      | false =>
          have admitted := SourceCurrentConjunctionEmptinessTable.admitted key SourceCurrentConjunctionWorklist.closed
            before.budget (queryTable before.table) nodes skipped
          have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
          obtain ⟨result, physical, stable, _effects, _resident, _bounded, _closed, afterFits⟩ :=
            SourceCurrentConjunctionTuplePullNumeric.sample_complete before.budget nodes
              before.storage.requirements.physical resource ready available closed fits
          cases result with
          | overflow tuples cursor =>
              exact ⟨.more, _, fun h enough => visit_overflow h nodes rest before physical tuples cursor
                empty skipped (stable h enough), afterFits⟩
          | fit tuples =>
              cases tuples with
              | nil =>
                  exact ⟨.more, _, fun h enough => visit_zero h nodes rest before physical
                    empty skipped (stable h enough), afterFits⟩
              | cons tuple tuples =>
                  exact ⟨.more, _, fun h enough => visit_positive h nodes rest before physical tuple tuples
                    empty skipped (stable h enough), afterFits⟩

/-- Current frame and heap facts derive one exact successful transition at explicit bounds. -/
theorem complete (bound : Nat) (before : Frame Symbol Formula bound) (resource : Nat)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before.state)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state)
    (queued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state)
    (fits : Fits resource before.state.storage.requirements.physical.heap) :
    ∃ event after,
      (∀ p h, projectionFuel before.state ≤ p → readerFuel before.state resource ≤ h →
        step p h before.state = .done event after) ∧
      Fits (forecast before.state resource) after.storage.requirements.physical.heap := by
  cases pending : before.state.pending with
  | nil =>
      refine ⟨.drained, before.state, fun p h _ _ => step_nil p h before.state pending, ?_⟩
      simpa only [forecast, pending] using fits
  | cons task rest =>
      cases task with
      | nodes nodes =>
          have available : Values before.state.storage.requirements.physical.heap nodes := by
            apply values.pending nodes
            rw [pending]
            exact List.mem_cons_self
          obtain ⟨event, after, stable, finalFits⟩ :=
            visit_complete nodes rest before.state resource values.ready available fits
          refine ⟨event, after, ?_, ?_⟩
          · intro p h _ enoughH
            rw [step_nodes p h before.state nodes rest pending]
            exact stable h (by simpa only [readerFuel, pending] using enoughH)
          · simpa only [forecast, pending] using finalFits
      | requirements handles =>
          cases handles with
          | nil =>
              refine ⟨.more, _, fun p h _ _ => step_requirements_nil p h before.state rest pending, ?_⟩
              simpa only [forecast, pending] using fits
          | cons handle handles =>
              have inside : handle < before.state.storage.requirements.cells.length := by
                apply queued.queued (handle :: handles) _ handle List.mem_cons_self
                rw [pending]
                exact List.mem_cons_self
              have present : ∃ cell, SourceCurrentConjunctionRequirementCells.lookup handle
                  before.state.storage.requirements = some cell :=
                ⟨before.state.storage.requirements.cells[handle],
                  List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
              obtain ⟨nodes, cells, stable, firstFits, effects, _cellValues, _cellClosed, available, _noFree⟩ :=
                SourceCurrentConjunctionRequirementCellsNumeric.complete handle before.state.storage.requirements resource
                  values.ready values.cells closed.cells fits present
              let firstResource := SourceCurrentConjunctionRequirementCellsNumeric.forecast handle
                before.state.storage.requirements resource
              let firstP := SourceCurrentConjunctionRequirementCellsNumeric.projectionFuel handle
                before.state.storage.requirements
              let firstH := SourceCurrentConjunctionRequirementCellsNumeric.readerFuel handle
                before.state.storage.requirements resource
              let count := SourceCurrentConjunctionRequirementCellsOutputBounds.bound handle
                before.state.storage.requirements
              have width : nodes.length ≤ count :=
                SourceCurrentConjunctionRequirementCellsOutputBounds.force_length
                  (stable firstP firstH (Nat.le_refl _) (Nat.le_refl _))
              let middle : WorkState := {before.state with storage := {before.state.storage with requirements := cells}}
              obtain ⟨event, after, visitStable, finalFits⟩ :=
                visit_complete nodes (.requirements handles :: rest) middle firstResource effects.ready available firstFits
              have wider : SourceCurrentConjunctionExposureResources.forecast nodes.length firstResource ≤
                  SourceCurrentConjunctionExposureResources.forecast count firstResource :=
                SourceCurrentConjunctionExposureResources.forecast_mono width (Nat.le_refl _)
              have fuelWidth : SourceCurrentConjunctionTuplePullNumeric.fuel nodes.length firstResource ≤
                  SourceCurrentConjunctionTuplePullNumeric.fuel count firstResource :=
                SourceCurrentProjectionUnionResources.readFuel_mono wider
              refine ⟨event, after, ?_, ?_⟩
              · intro p h enoughP enoughH
                have enoughProjection : firstP ≤ p := by
                  simpa only [projectionFuel, pending] using enoughP
                have enoughRead : max firstH (SourceCurrentConjunctionTuplePullNumeric.fuel count firstResource) ≤ h := by
                  simpa only [readerFuel, pending] using enoughH
                have forced := stable p h enoughProjection
                  (Nat.le_trans (Nat.le_max_left _ _) enoughRead)
                rw [step_requirement_done p h handle handles before.state rest nodes cells pending forced]
                exact visitStable h (Nat.le_trans fuelWidth (Nat.le_trans (Nat.le_max_right _ _) enoughRead))
              · simpa only [forecast, pending] using finalFits.mono wider
      | rows handle =>
          have member : Task.rows handle ∈ before.state.pending := by
            rw [pending]
            exact List.mem_cons_self
          obtain ⟨credit, found⟩ := before.present handle member
          have inside : handle < before.state.storage.spines.length := by
            rw [← before.valid.length]
            exact (List.getElem?_eq_some_iff.mp found).1
          have present : ∃ spine, SourceCurrentConjunctionRequirementRows.lookupSpine handle
              before.state.storage = some spine :=
            ⟨before.state.storage.spines[handle], List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
          obtain ⟨row, storage, actual⟩ := SourceCurrentConjunctionRequirementRowsCompletion.nextRow_success
            handle before.state.storage values.ready values.raw present
          have sameHeap := SourceCurrentConjunctionRequirementRowsProbes.nextRow_heap handle before.state.storage
          rw [actual] at sameHeap
          change storage.requirements.physical.heap = before.state.storage.requirements.physical.heap at sameHeap
          have finalFits : Fits resource storage.requirements.physical.heap := by
            rw [sameHeap]
            exact fits
          cases row with
          | none =>
              refine ⟨.more, _, fun p h _ _ =>
                step_rows_none p h handle before.state rest storage pending actual, ?_⟩
              simpa only [forecast, pending] using finalFits
          | some row =>
              rcases row with ⟨handles, tail⟩
              refine ⟨.more, _, fun p h _ _ =>
                step_rows_live p h handle tail before.state rest handles storage pending actual, ?_⟩
              simpa only [forecast, pending] using finalFits

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStepNumeric
