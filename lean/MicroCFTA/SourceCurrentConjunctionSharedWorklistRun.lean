import MicroCFTA.SourceCurrentConjunctionSharedWorklistFrame
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStepProgress

/-!
# Finite iteration of actual shared worklist transitions

The original tuple budget determines the private rank vector. Every continuing
transition lowers that rank. The iterator has no additional fuel argument.
Its execution graph retains exact actual failures and drained private states.
Table materialization, Boolean soundness, and selected caller adoption remain
separate obligations. Native observation allowances remain explicit.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- The internal rank uses the remaining budget and the fixed original vector. -/
def rank {bound : Nat} (before : Frame Symbol Formula bound) : Nat × (Fin (bound + 2) → Nat) :=
  (before.state.budget, SourceCurrentConjunctionSharedWorklistWeight.rank bound before.credits before.state.pending)

/-- This order uses only the internally derived rank of each private frame. -/
def Below (bound : Nat) (first last : Frame Symbol Formula bound) : Prop :=
  Prod.Lex (fun first last : Nat => first < last) (HeightOrder.VectorBelow (bound + 2))
    (rank first) (rank last)

/-- The existing finite-vector order gives well-founded private-frame iteration. -/
theorem wellFounded (bound : Nat) : WellFounded (Below (Symbol := Symbol) (Formula := Formula) bound) :=
  InvImage.wf rank
    (Prod.lex Nat.lt_wfRel
      ⟨HeightOrder.VectorBelow (bound + 2), HeightOrder.vector_wellFounded (bound + 2)⟩).wf

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private noncomputable def nextAdded (bound p h : Nat) (before : Frame Symbol Formula bound) : List Nat :=
  Classical.choose (SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h before)

private noncomputable def nextFrame (bound p h : Nat) (before : Frame Symbol Formula bound) : Frame Symbol Formula bound :=
  Classical.choose (Classical.choose_spec
    (SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h before))

private theorem nextFrame_facts (bound p h : Nat) (before : Frame Symbol Formula bound) :
    (nextFrame bound p h before).state = (step p h before.state).state ∧
      (nextFrame bound p h before).credits = before.credits ++ nextAdded bound p h before :=
  Classical.choose_spec (Classical.choose_spec
    (SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h before))

private theorem nextFrame_smaller (bound p h : Nat) (before : Frame Symbol Formula bound)
    (after : State Symbol Formula) (actual : step p h before.state = .done .more after) :
    Below bound (nextFrame bound p h before) before := by
  have facts := nextFrame_facts bound p h before
  have stateSame : (nextFrame bound p h before).state = after := by
    simpa only [actual, Outcome.state] using facts.1
  have valid : SourceCurrentConjunctionRequirementRowsOrigins.Credits
      (before.credits ++ nextAdded bound p h before) after.storage := by
    rw [← facts.2, ← stateSame]
    exact (nextFrame bound p h before).valid
  have lower := SourceCurrentConjunctionSharedWorklistStepProgress.step_decreases bound p h
    before.credits (nextAdded bound p h before) before.state after before.bounded before.present actual valid
  change Prod.Lex _ _
    ((nextFrame bound p h before).state.budget,
      SourceCurrentConjunctionSharedWorklistWeight.rank bound (nextFrame bound p h before).credits
        (nextFrame bound p h before).state.pending)
    (before.state.budget, SourceCurrentConjunctionSharedWorklistWeight.rank bound before.credits before.state.pending)
  rw [stateSame, facts.2]
  exact lower

private noncomputable def body (bound p h : Nat) (before : Frame Symbol Formula bound)
    (recur : ∀ after : Frame Symbol Formula bound, Below bound after before → Outcome Symbol Formula) :
    Outcome Symbol Formula :=
  match actual : step p h before.state with
  | .failed fault after => .failed fault after
  | .done .drained after => .done .drained after
  | .done .more after => recur (nextFrame bound p h before) (nextFrame_smaller bound p h before after actual)

/-- Iterate the actual transitions without a caller-supplied work allowance. -/
noncomputable def run (bound p h : Nat) (before : Frame Symbol Formula bound) : Outcome Symbol Formula :=
  (wellFounded bound).fix (body bound p h) before

private theorem run_eq (bound p h : Nat) (before : Frame Symbol Formula bound) :
    run bound p h before = body bound p h before (fun after _ => run bound p h after) :=
  WellFounded.fix_eq (wellFounded bound) (body bound p h) before

private theorem run_step (bound p h : Nat) (before : Frame Symbol Formula bound) :
    run bound p h before =
      match step p h before.state with
      | .failed fault after => .failed fault after
      | .done .drained after => .done .drained after
      | .done .more _ => run bound p h (nextFrame bound p h before) := by
  rw [run_eq]
  unfold body
  split <;> rename_i actual <;> simp only [actual]

/-- Each graph edge is the exact actual shared transition at its reached state. -/
inductive Run (p h : Nat) : State Symbol Formula → Outcome Symbol Formula → Prop where
  | failed {before after : State Symbol Formula} {fault : Fault Symbol Formula}
      (actual : step p h before = .failed fault after) : Run p h before (.failed fault after)
  | drained {before after : State Symbol Formula}
      (actual : step p h before = .done .drained after) : Run p h before (.done .drained after)
  | more {before middle : State Symbol Formula} {outcome : Outcome Symbol Formula}
      (actual : step p h before = .done .more middle)
      (tail : Run p h middle outcome) : Run p h before outcome

/-- The total iterator derives its own finite actual execution graph. -/
theorem run_graph (bound p h : Nat) (before : Frame Symbol Formula bound) :
    Run p h before.state (run bound p h before) := by
  induction before using (wellFounded bound).induction with
  | h before ih =>
      rw [run_step]
      cases actual : step p h before.state with
      | failed fault after =>
          exact Run.failed actual
      | done event after =>
          cases event with
          | drained =>
              exact Run.drained actual
          | more =>
              have tail := ih (nextFrame bound p h before) (nextFrame_smaller bound p h before after actual)
              have stateSame : (nextFrame bound p h before).state = after := by
                simpa only [actual, Outcome.state] using (nextFrame_facts bound p h before).1
              exact Run.more actual (stateSame ▸ tail)

/-- Start from the original query, budget, and physical state with empty private storage. -/
noncomputable def explore (p h budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) : Outcome Symbol Formula :=
  run budget p h (SourceCurrentConjunctionSharedWorklistFrame.initial budget start before)

/-- Original initialization derives a finite actual graph without a future rank or heap. -/
theorem explore_graph (p h budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Run p h (SourceCurrentConjunctionSharedWorklistStep.initial budget start before)
      (explore p h budget start before) :=
  run_graph budget p h (SourceCurrentConjunctionSharedWorklistFrame.initial budget start before)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistRun
