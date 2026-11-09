import MicroCFTA.SourceCurrentConjunctionSharedWorklistRun

/-!
# Internal frames at actual shared-worklist endpoints

Every finite execution carries its derived frame through each actual step.
Original initialization supplies the first frame. Successful and failed
endpoints both retain their own credits and fixed original budget bound.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistRunFrame
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
open SourceCurrentConjunctionSharedWorklistRun

variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem graph_frame {bound p h : Nat}
    {before : SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula}
    {outcome : Outcome Symbol Formula} (actual : Run p h before outcome) :
    (∃ frame : Frame Symbol Formula bound, frame.state = before) →
      ∃ frame : Frame Symbol Formula bound, frame.state = outcome.state := by
  induction actual with
  | failed observed =>
      rintro ⟨frame, same⟩
      obtain ⟨_, next, stateSame, _⟩ :=
        SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h frame
      rw [same, observed] at stateSame
      exact ⟨next, stateSame⟩
  | drained observed =>
      rintro ⟨frame, same⟩
      obtain ⟨_, next, stateSame, _⟩ :=
        SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h frame
      rw [same, observed] at stateSame
      exact ⟨next, stateSame⟩
  | more observed _ ih =>
      rintro ⟨frame, same⟩
      obtain ⟨_, next, stateSame, _⟩ :=
        SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h frame
      rw [same, observed] at stateSame
      exact ih ⟨next, stateSame⟩

/-- The actual iterator endpoint has a frame at its original fixed bound. -/
theorem run_frame (bound p h : Nat) (before : Frame Symbol Formula bound) :
    ∃ after : Frame Symbol Formula bound, after.state = (run bound p h before).state :=
  graph_frame (run_graph bound p h before) ⟨before, rfl⟩

/-- Original query initialization derives the endpoint frame without a future certificate. -/
theorem explore_frame (p h budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    ∃ after : Frame Symbol Formula budget, after.state = (explore p h budget start before).state :=
  graph_frame (explore_graph p h budget start before)
    ⟨SourceCurrentConjunctionSharedWorklistFrame.initial budget start before, rfl⟩

private theorem visit_ne_drained (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before after : State Symbol Formula)
    (actual : visit h nodes rest before = .done .drained after) : False := by
  unfold visit at actual
  split at actual
  · cases actual
  · split at actual
    · cases actual
    · split at actual <;> cases actual

private theorem step_drained_pending (p h : Nat) (before after : State Symbol Formula)
    (actual : step p h before = .done .drained after) : after.pending = [] := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact pending
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at actual
          exact False.elim (visit_ne_drained h nodes rest before after actual)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  exact False.elim (visit_ne_drained h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}} after actual)
      | rows handle =>
          cases observed : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending observed] at actual
              cases actual
          | done row storage =>
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending observed] at actual
                  cases actual
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending observed] at actual
                  cases actual

private theorem graph_drained_pending {p h : Nat} {before : State Symbol Formula}
    {outcome : Outcome Symbol Formula} (actual : Run p h before outcome) :
    ∀ after, outcome = .done .drained after → after.pending = [] := by
  induction actual with
  | failed _ =>
      intro after same
      cases same
  | drained observed =>
      intro after same
      cases same
      exact step_drained_pending p h _ _ observed
  | more _ _ ih => exact ih

/-- A successful original exploration drains its actual queue before it returns. -/
theorem explore_done_pending (p h budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula)
    (after : State Symbol Formula)
    (actual : explore p h budget start before = .done .drained after) : after.pending = [] :=
  graph_drained_pending (explore_graph p h budget start before) after actual

end MicroCFTA.SourceCurrentConjunctionSharedWorklistRunFrame
