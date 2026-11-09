import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Stable completion of a present requirement cell

A successful force keeps the same result and complete private state when
both worker bounds increase. Current readiness and resident closed cell
operands supply finite bounds for every present handle. The proof follows
the actual job order and stops at the first Empty result.

These bounds are proof observations. This module does not prove numeric
capacity, validity of queued handles, or adoption by a selected caller.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsCompletion
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementPull (Cursor projection step)
open SourceCurrentConjunctionRequirementCells
open SourceCurrentConjunctionRequirements (canonical isEmpty)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem projection_done_stable {p h P H : Nat} {job : Job Symbol Formula}
    {before after : Physical Symbol Formula} {value : Node}
    (actual : projection p h job before = .done value after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    projection P H job before = .done value after := by
  have singleton : SourceCurrentConjunctionRowsWorker.projections p h [job] before =
      .done [value] after := by
    rw [← SourceCurrentConjunctionRequirementPull.projection_singleton, actual]
    rfl
  have stable := SourceCurrentConjunctionRowsWorkerStability.projections_done_stable
    singleton enoughP enoughH
  unfold projection
  rw [stable]
  rfl

private theorem pull_step_done_stable {p h P H : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula}
    {event : SourceCurrentConjunctionRequirementPull.Event Symbol Formula}
    (actual : step p h cursor before = .done event after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    step P H cursor before = .done event after := by
  rcases cursor with ⟨jobs, collected⟩
  cases jobs with
  | nil => simpa only [step] using actual
  | cons job rest =>
      cases projected : projection p h job before with
      | failed fault physical =>
          simp only [step, projected, SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
          cases actual
      | done value physical =>
          have stable := projection_done_stable projected enoughP enoughH
          simp only [step, projected, SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
          simpa only [step, stable, SourceCurrentConjunctionRowsWorker.Outcome.bind] using actual

private theorem forceStep_done_stable {p h P H handle : Nat} {before after : Cells}
    {event : Event Symbol Formula}
    (actual : forceStep p h handle before = .done event after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    forceStep P H handle before = .done event after := by
  cases found : lookup handle before with
  | none => simpa only [forceStep, found] using actual
  | some cell =>
      cases cell with
      | done nodes => simpa only [forceStep, found] using actual
      | column nodes => simpa only [forceStep, found] using actual
      | pending cursor =>
          cases observed : step p h cursor before.physical with
          | failed fault physical =>
              simp only [forceStep, found, observed] at actual
              cases actual
          | done event physical =>
              have stable := pull_step_done_stable observed enoughP enoughH
              simp only [forceStep, found, observed] at actual
              simpa only [forceStep, found, stable] using actual

/-- Larger independent bounds replay a successful force with its identical complete cell state. -/
theorem force_done_stable {p h P H handle : Nat} {before after : Cells} {nodes : List Node}
    (actual : force p h handle before = .done nodes after)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    force P H handle before = .done nodes after := by
  suffices ∀ weight (current : Cells), remaining handle current = weight →
      ∀ output final, force p h handle current = .done output final →
        force P H handle current = .done output final by
    exact this _ before rfl nodes after actual
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured output final completed
      rw [force_step] at completed ⊢
      cases observed : forceStep p h handle current with
      | failed fault physical =>
          simp only [observed] at completed
          cases completed
      | done event physical =>
          have stable := forceStep_done_stable observed enoughP enoughH
          rw [stable]
          cases event with
          | complete result =>
              simpa only [observed] using completed
          | more cursor =>
              simp only [observed] at completed
              have decrease : remaining handle physical < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current physical cursor observed
              exact smaller _ decrease physical rfl output final completed

private theorem projection_complete (job : Job Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap job.1) (closed : ClosedValues job.1) :
    ∃ p h value after, projection p h job before = .done value after := by
  rcases job with ⟨forest, path⟩
  obtain ⟨value, heap, trace, _⟩ := SourceEqualityProjectionComplete.forest_complete
    (path.map Int.ofNat) forest before.heap ready.semantic available closed
  obtain ⟨p, h, stable⟩ := SourceEqualityProjectionWorkerComplete.forest_stable trace
  refine ⟨p, h, value, ⟨heap, before.equality⟩, ?_⟩
  simp only [projection, SourceCurrentConjunctionRowsWorker.projections,
    stable p h (Nat.le_refl _) (Nat.le_refl _), SourceCurrentConjunctionRowsWorker.Outcome.bind,
    List.headD_cons]

private theorem force_exists (handle : Nat) (before : Cells) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (present : ∃ cell, lookup handle before = some cell) :
    ∃ p h nodes after, force p h handle before = .done nodes after := by
  suffices ∀ weight (current : Cells), remaining handle current = weight →
      Ready current.physical → SourceCurrentConjunctionRequirementCellsValues.Invariant current →
      SourceCurrentConjunctionRequirementCellsClosed.Invariant current →
      (∃ cell, lookup handle current = some cell) →
        ∃ p h nodes after, force p h handle current = .done nodes after by
    exact this _ before rfl ready values closed present
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured ready values closed present
      cases found : lookup handle current with
      | none =>
          obtain ⟨cell, stored⟩ := present
          rw [found] at stored
          cases stored
      | some cell =>
          cases cell with
          | done nodes => exact ⟨0, 0, nodes, current, force_hit 0 0 handle nodes current found⟩
          | column nodes =>
              refine ⟨0, 0, canonical nodes, update handle (.done (canonical nodes)) current, ?_⟩
              rw [force_step]
              simp only [forceStep, found]
          | pending cursor =>
              rcases cursor with ⟨jobs, collected⟩
              cases jobs with
              | nil =>
                  refine ⟨0, 0, canonical collected, update handle (.done (canonical collected)) current, ?_⟩
                  rw [force_step]
                  simp only [forceStep, found, step]
              | cons job rest =>
                  have own := values handle _ found
                  have ownClosed := closed handle _ found
                  obtain ⟨p, h, value, physical, projected⟩ := projection_complete job current.physical ready
                    (own.2 job List.mem_cons_self) (ownClosed.2 job List.mem_cons_self)
                  cases tested : isEmpty value with
                  | true =>
                      let after := update handle (.done [.empty]) {current with physical := physical}
                      refine ⟨p, h, [.empty], after, ?_⟩
                      rw [force_step]
                      simp only [forceStep, found, step, projected,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, ite_true]
                      rfl
                  | false =>
                      let next : Cursor Symbol Formula := ⟨rest, collected ++ [value]⟩
                      let middle := update handle (.pending next) {current with physical := physical}
                      have first : forceStep p h handle current = .done (.more next) middle := by
                        simp only [forceStep, found, step, projected,
                          SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, Bool.false_eq_true, ite_false]
                        rfl
                      have kept : Effects current.physical middle.physical ∧
                          SourceCurrentConjunctionRequirementCellsValues.Invariant middle ∧
                          SourceCurrentConjunctionRequirementCellsValues.EventValues middle.physical.heap (.more next) := by
                        simpa only [first, Outcome.state] using
                          SourceCurrentConjunctionRequirementCellsValues.forceStep_values p h handle current ready values
                      have closedNext : SourceCurrentConjunctionRequirementCellsClosed.Invariant middle ∧
                          SourceCurrentConjunctionRequirementCellsClosed.EventClosed (.more next) := by
                        simpa only [first, Outcome.state] using
                          SourceCurrentConjunctionRequirementCellsClosed.forceStep_closed p h handle current ready values closed
                      have foundNext : lookup handle middle = some (.pending next) :=
                        lookup_update handle (.pending ⟨job :: rest, collected⟩) (.pending next)
                          {current with physical := physical} found
                      have decrease : remaining handle middle < weight := by
                        rw [← measured]
                        exact forceStep_more_decreases p h handle current middle next first
                      obtain ⟨nextP, nextH, nodes, after, completed⟩ :=
                        smaller _ decrease middle rfl kept.1.ready kept.2.1 closedNext.1 ⟨_, foundNext⟩
                      have firstStable := forceStep_done_stable first
                        (Nat.le_max_left p nextP) (Nat.le_max_left h nextH)
                      have restStable := force_done_stable completed
                        (Nat.le_max_right p nextP) (Nat.le_max_right h nextH)
                      refine ⟨max p nextP, max h nextH, nodes, after, ?_⟩
                      rw [force_step, firstStable]
                      exact restStable

/-- Current resident closed operands give stable completion and actual effects for every present cell. -/
theorem force_complete (handle : Nat) (before : Cells) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (closed : SourceCurrentConjunctionRequirementCellsClosed.Invariant before)
    (present : ∃ cell, lookup handle before = some cell) :
    ∃ p h nodes after,
      (∀ P H, p ≤ P → h ≤ H → force P H handle before = .done nodes after) ∧
      Effects before.physical after.physical ∧
      SourceCurrentConjunctionRequirementCellsValues.Invariant after ∧
      SourceCurrentConjunctionRequirementCellsClosed.Invariant after ∧
      Values after.physical.heap nodes ∧ ClosedValues nodes := by
  obtain ⟨p, h, nodes, after, actual⟩ := force_exists handle before ready values closed present
  have kept : Effects before.physical after.physical ∧
      SourceCurrentConjunctionRequirementCellsValues.Invariant after ∧ Values after.physical.heap nodes := by
    simpa only [actual, Outcome.state] using
      SourceCurrentConjunctionRequirementCellsValues.force_values p h handle before ready values
  have finalClosed : SourceCurrentConjunctionRequirementCellsClosed.Invariant after ∧ ClosedValues nodes := by
    simpa only [actual, Outcome.state] using
      SourceCurrentConjunctionRequirementCellsClosed.force_closed p h handle before ready values closed
  exact ⟨p, h, nodes, after, fun _ _ enoughP enoughH => force_done_stable actual enoughP enoughH,
    kept.1, kept.2.1, finalClosed.1, kept.2.2, finalClosed.2⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsCompletion
