import MicroCFTA.SourceCurrentConjunctionTuplePullTotal
import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability

set_option autoImplicit false

/-!
Larger read allowances preserve successful cursor observations exactly.
The result includes the complete physical heap and equality cache.
Finite suspended statuses also remain exact. Total sampling derives its
finite observation internally. This module makes no fault-stability claim.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullStability
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsWorkerStability (bind_done_iff exposures_done_stable)
open SourceCurrentConjunctionTuplePull (Cursor Event expose step)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
open SourceCurrentConjunctionTuplePullTotal (Result)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
/-- A larger read allowance preserves an actual successful singleton read. -/
theorem expose_done_stable {h largerH : Nat} {node : Node} {before after : Physical Symbol Formula}
    {rows : List Edge} (actual : expose h node before = .done rows after) (enough : h ≤ largerH) :
    expose largerH node before = .done rows after := by
  obtain ⟨exposed, middle, first, returned⟩ := (bind_done_iff _ _ rows after).mp actual
  simp only [expose, exposures_done_stable first enough, Outcome.bind]
  exact returned

/-- Every successful transition keeps its event, continuation, and complete state. -/
theorem step_done_stable {h largerH : Nat} {cursor : Cursor Symbol Formula}
    {before after : Physical Symbol Formula} {event : Event Symbol Formula}
    (actual : step h cursor before = .done event after) (enough : h ≤ largerH) :
    step largerH cursor before = .done event after := by
  induction cursor generalizing before after event with
  | empty => exact actual
  | seed node =>
      cases observed : expose h node before with
      | failed fault middle => simp only [step, observed, Outcome.bind] at actual; cases actual
      | done rows middle =>
          simp only [step, observed, Outcome.bind] at actual
          simpa only [step, expose_done_stable observed enough, Outcome.bind] using actual
  | seedRows rows => cases rows <;> exact actual
  | extend node inner ih =>
      cases observed : step h inner before with
      | failed fault middle => simp only [step, observed, Outcome.bind] at actual; cases actual
      | done result middle =>
          simp only [step, observed, Outcome.bind] at actual
          simpa only [step, ih observed, Outcome.bind] using actual
  | readOperand node inner tuple ih =>
      cases tuple with
      | nil => exact actual
      | cons first rest =>
          cases observed : expose h node before with
          | failed fault middle => simp only [step, observed, Outcome.bind] at actual; cases actual
          | done rows middle =>
              simp only [step, observed, Outcome.bind] at actual
              simpa only [step, expose_done_stable observed enough, Outcome.bind] using actual
  | scanOperand node inner tuple remaining ih =>
      cases tuple with
      | nil => exact actual
      | cons first rest => cases remaining <;> exact actual

/-- Successful finite sampling keeps the same cap test and status. -/
theorem advance_done_stable {h largerH budget : Nat} {cursor : Cursor Symbol Formula}
    {collected : List (List Edge)} {before after : Physical Symbol Formula} {status : Status Symbol Formula}
    (actual : advance h budget cursor collected before = .done status after) (enough : h ≤ largerH) :
    advance largerH budget cursor collected before = .done status after := by
  obtain ⟨event, middle, first, returned⟩ := (bind_done_iff _ _ status after).mp actual
  simp only [advance, step_done_stable first enough, Outcome.bind]
  exact returned

/-- Larger read fuel preserves all successful finite drives, including suspension. -/
theorem drive_done_stable (steps : Nat) {h largerH budget : Nat} {cursor : Cursor Symbol Formula}
    {collected : List (List Edge)} {before after : Physical Symbol Formula} {status : Status Symbol Formula}
    (actual : drive steps h budget cursor collected before = .done status after) (enough : h ≤ largerH) :
    drive steps largerH budget cursor collected before = .done status after := by
  induction steps generalizing cursor collected before status after with
  | zero => exact actual
  | succ steps ih =>
      obtain ⟨result, middle, first, later⟩ := (bind_done_iff _ _ status after).mp actual
      simp only [drive, advance_done_stable first enough, Outcome.bind]
      cases result with
      | running next sampled => exact ih later
      | fit sampled | overflow sampled next => exact later

/-- Total successful sampling has the same result and state at every larger read allowance. -/
theorem run_done_stable {h largerH budget : Nat} {cursor : Cursor Symbol Formula}
    {collected : List (List Edge)} {before after : Physical Symbol Formula} {result : Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.run h budget cursor collected before = .done result after)
    (enough : h ≤ largerH) :
    SourceCurrentConjunctionTuplePullTotal.run largerH budget cursor collected before = .done result after := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.run_observation h budget cursor collected before
  have observed := eventual 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe] at observed
  exact SourceCurrentConjunctionTuplePullTotal.run_of_observation steps largerH budget cursor collected before
    (.done result after) (drive_done_stable steps observed enough)

/-- Actual total startup needs no caller transition bound or physical invariant. -/
theorem sample_done_stable {h largerH budget : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {result : Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (enough : h ≤ largerH) :
    SourceCurrentConjunctionTuplePullTotal.sample largerH budget nodes before = .done result after :=
  run_done_stable actual enough

end MicroCFTA.SourceCurrentConjunctionTuplePullStability
