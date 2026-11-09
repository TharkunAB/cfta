import MicroCFTA.SourceCurrentConjunctionSharedWorklistStability
import MicroCFTA.SourceCurrentConjunctionSharedWorklistQueuedHandles
import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed
import MicroCFTA.SourceCurrentConjunctionRequirementRowsCompletion
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalCompletion

/-!
# Stable completion of the original shared worklist

Current physical readiness and the available starting query derive finite
successful observation bounds. Each continuing transition lowers the
existing rank with the original budget as its fixed vector bound. The proof
retains the actual private state and combines bounds in execution order.

Open queries can stop at the actual skip test. Only admitted sampling needs
closed operands. These existential bounds do not establish numeric capacity
or select a new checked caller.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistCompletion
open InternedConstructorTemplates (Value EdgeKey)
open InternedNestedProvenance (Values)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistRun (Run Below wellFounded)
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
variable {Symbol Formula : Type}
local notation "Node" => Value Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_success (nodes : List Node) (rest : List (Task Symbol Formula)) (before : WorkState)
    (ready : Ready before.storage.requirements.physical)
    (available : Values before.storage.requirements.physical.heap nodes) :
    ∃ h event after, visit h nodes rest before = .done event after := by
  cases empty : nodes.any isEmpty with
  | true => exact ⟨0, .more, _, visit_empty 0 nodes rest before empty⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true => exact ⟨0, .more, _, visit_skip 0 nodes rest before empty skipped⟩
      | false =>
          have admitted := SourceCurrentConjunctionEmptinessTable.admitted key SourceCurrentConjunctionWorklist.closed
            before.budget (queryTable before.table) nodes skipped
          have closed := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
          obtain ⟨h, result, physical, stable, _⟩ :=
            SourceCurrentConjunctionTuplePullTotalCompletion.sample_complete before.budget nodes
              before.storage.requirements.physical ready available closed
          have sampled := stable h (Nat.le_refl _)
          cases result with
          | overflow tuples cursor =>
              exact ⟨h, .more, _, visit_overflow h nodes rest before physical tuples cursor empty skipped sampled⟩
          | fit tuples =>
              cases tuples with
              | nil => exact ⟨h, .more, _, visit_zero h nodes rest before physical empty skipped sampled⟩
              | cons tuple tuples =>
                  exact ⟨h, .more, _, visit_positive h nodes rest before physical tuple tuples empty skipped sampled⟩

private theorem step_success (bound : Nat) (before : Frame Symbol Formula bound)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before.state)
    (closed : SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state)
    (queued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state) :
    ∃ p h event after, step p h before.state = .done event after := by
  cases pending : before.state.pending with
  | nil => exact ⟨0, 0, .drained, _, step_nil 0 0 before.state pending⟩
  | cons task rest =>
      cases task with
      | nodes nodes =>
          have available : Values before.state.storage.requirements.physical.heap nodes := by
            apply values.pending nodes
            rw [pending]
            exact List.mem_cons_self
          obtain ⟨h, event, after, actual⟩ := visit_success nodes rest before.state values.ready available
          exact ⟨0, h, event, after, by rw [step_nodes 0 h before.state nodes rest pending]; exact actual⟩
      | requirements handles =>
          cases handles with
          | nil => exact ⟨0, 0, .more, _, step_requirements_nil 0 0 before.state rest pending⟩
          | cons handle handles =>
              have inside : handle < before.state.storage.requirements.cells.length := by
                apply queued.queued (handle :: handles) _ handle List.mem_cons_self
                rw [pending]
                exact List.mem_cons_self
              have present : ∃ cell, SourceCurrentConjunctionRequirementCells.lookup handle
                  before.state.storage.requirements = some cell :=
                ⟨before.state.storage.requirements.cells[handle],
                  List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
              obtain ⟨p, h, nodes, cells, stable, effects, _, _, available, _⟩ :=
                SourceCurrentConjunctionRequirementCellsCompletion.force_complete handle
                  before.state.storage.requirements values.ready values.cells closed.cells present
              let middle : WorkState := {before.state with storage := {before.state.storage with requirements := cells}}
              obtain ⟨nextH, event, after, actual⟩ :=
                visit_success nodes (.requirements handles :: rest) middle effects.ready available
              have forced := stable p (max h nextH) (Nat.le_refl _) (Nat.le_max_left _ _)
              refine ⟨p, max h nextH, event, after, ?_⟩
              rw [step_requirement_done p (max h nextH) handle handles before.state rest nodes cells pending forced]
              exact SourceCurrentConjunctionSharedWorklistStability.visit_done_stable actual (Nat.le_max_right _ _)
      | rows handle =>
          have member : Task.rows handle ∈ before.state.pending := by
            rw [pending]
            exact List.mem_cons_self
          obtain ⟨credit, found⟩ := before.present handle member
          have inside : handle < before.state.storage.spines.length := by
            rw [← before.valid.length]
            exact (List.getElem?_eq_some_iff.mp found).1
          have present : ∃ spine, SourceCurrentConjunctionRequirementRows.lookupSpine handle before.state.storage = some spine :=
            ⟨before.state.storage.spines[handle], List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
          obtain ⟨row, storage, actual⟩ := SourceCurrentConjunctionRequirementRowsCompletion.nextRow_success
            handle before.state.storage values.ready values.raw present
          cases row with
          | none => exact ⟨0, 0, .more, _, step_rows_none 0 0 handle before.state rest storage pending actual⟩
          | some row =>
              rcases row with ⟨handles, tail⟩
              exact ⟨0, 0, .more, _, step_rows_live 0 0 handle tail before.state rest handles storage pending actual⟩

private theorem frame_complete (bound : Nat) (before : Frame Symbol Formula bound) :
    SourceCurrentConjunctionSharedWorklistValues.Invariant before.state →
    SourceCurrentConjunctionSharedWorklistClosed.Invariant before.state →
    SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant before.state →
      ∃ p h after, ∀ P H, p ≤ P → h ≤ H → Run P H before.state (.done .drained after) := by
  apply (wellFounded bound).induction before
  intro before ih values closed queued
  obtain ⟨p, h, event, middle, actual⟩ := step_success bound before values closed queued
  cases event with
  | drained =>
      exact ⟨p, h, middle, fun _ _ enoughP enoughH =>
        Run.drained (SourceCurrentConjunctionSharedWorklistStability.step_done_stable actual enoughP enoughH)⟩
  | more =>
      obtain ⟨added, next, stateEquation, creditsEquation⟩ :=
        SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h before
      have stateSame : next.state = middle := by
        simpa only [actual, Outcome.state] using stateEquation
      have valid : SourceCurrentConjunctionRequirementRowsOrigins.Credits
          (before.credits ++ added) middle.storage := by
        rw [← creditsEquation, ← stateSame]
        exact next.valid
      have lower := SourceCurrentConjunctionSharedWorklistStepProgress.step_decreases bound p h
        before.credits added before.state middle before.bounded before.present actual valid
      have smaller : Below bound next before := by
        change Prod.Lex _ _
          (next.state.budget, SourceCurrentConjunctionSharedWorklistWeight.rank bound next.credits next.state.pending)
          (before.state.budget, SourceCurrentConjunctionSharedWorklistWeight.rank bound before.credits before.state.pending)
        rw [stateSame, creditsEquation]
        exact lower
      have nextValues : SourceCurrentConjunctionSharedWorklistValues.Invariant next.state := by
        rw [stateSame]
        simpa only [actual, Outcome.state] using
          (SourceCurrentConjunctionSharedWorklistValues.step_values p h before.state values).2
      have nextClosed : SourceCurrentConjunctionSharedWorklistClosed.Invariant next.state := by
        rw [stateSame]
        simpa only [actual, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistClosed.step_closed p h before.state values closed
      have nextQueued : SourceCurrentConjunctionSharedWorklistQueuedHandles.Invariant next.state := by
        rw [stateSame]
        simpa only [actual, Outcome.state] using
          SourceCurrentConjunctionSharedWorklistQueuedHandles.step_preserves p h before.state queued
      obtain ⟨tailP, tailH, after, stable⟩ := ih next smaller nextValues nextClosed nextQueued
      refine ⟨max p tailP, max h tailH, after, ?_⟩
      intro P H enoughP enoughH
      refine Run.more (SourceCurrentConjunctionSharedWorklistStability.step_done_stable actual
        (Nat.le_trans (Nat.le_max_left _ _) enoughP) (Nat.le_trans (Nat.le_max_left _ _) enoughH)) ?_
      have tail := stable P H (Nat.le_trans (Nat.le_max_right _ _) enoughP)
        (Nat.le_trans (Nat.le_max_right _ _) enoughH)
      rw [stateSame] at tail
      exact tail

private theorem run_unique {p h : Nat} {before : WorkState}
    {first second : Outcome Symbol Formula} (one : Run p h before first)
    (two : Run p h before second) : first = second := by
  induction one generalizing second with
  | failed actual =>
      cases two with
      | failed other => exact actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | drained actual =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => exact actual.symm.trans other
      | more other tail => cases actual.symm.trans other
  | more actual tail ih =>
      cases two with
      | failed other => cases actual.symm.trans other
      | drained other => cases actual.symm.trans other
      | more other rest =>
          have same := Outcome.done.inj (actual.symm.trans other)
          cases same.2
          exact ih rest

/-- Original initialization derives a single drained state at every sufficiently large pair of observation bounds. -/
theorem explore_initial (budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ p h after, ∀ P H, p ≤ P → h ≤ H →
      SourceCurrentConjunctionSharedWorklistRun.explore P H budget start before = .done .drained after := by
  obtain ⟨p, h, after, stable⟩ := frame_complete budget
    (SourceCurrentConjunctionSharedWorklistFrame.initial budget start before)
    (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
    (SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before)
    (SourceCurrentConjunctionSharedWorklistQueuedHandles.initial budget start before)
  refine ⟨p, h, after, ?_⟩
  intro P H enoughP enoughH
  exact (run_unique (stable P H enoughP enoughH)
    (SourceCurrentConjunctionSharedWorklistRun.explore_graph P H budget start before)).symm

end MicroCFTA.SourceCurrentConjunctionSharedWorklistCompletion
