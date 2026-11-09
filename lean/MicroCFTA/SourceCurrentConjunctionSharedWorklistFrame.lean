import MicroCFTA.SourceCurrentConjunctionSharedWorklistCreditBounds
import MicroCFTA.SourceCurrentConjunctionSharedWorklistRefs

/-!
# Internal certificates for actual shared worklist states

The original tuple budget fixes the vector dimension. Initial allocation
constructs the certificate. Each actual transition derives its next credit
suffix and certificate. The public caller supplies no future rank or heap.
These certificates do not yet prove queue drain or table materialization.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistFrame
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
open SourceCurrentConjunctionSharedWorklistWeight (RowsPresent)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- The private rank data and proofs accompany the exact actual worklist state. -/
structure Frame (Symbol Formula : Type) (bound : Nat) where
  state : State Symbol Formula
  credits : List Nat
  valid : Credits credits state.storage
  bounded : ∀ credit ∈ credits, credit ≤ bound
  budget : state.budget ≤ bound
  present : RowsPresent credits state.pending

/-- Original allocation derives every internal certificate field. -/
def initial (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) : Frame Symbol Formula budget :=
  { state := SourceCurrentConjunctionSharedWorklistStep.initial budget start before
    credits := []
    valid := (SourceCurrentConjunctionSharedWorklistCreditBounds.initial_bounded budget start before).1
    bounded := by intro credit member; cases member
    budget := Nat.le_refl _
    present := SourceCurrentConjunctionSharedWorklistRefs.initial_present budget start before }

/-- The certified initial state is exactly the actual source initialization. -/
theorem initial_state (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    (initial budget start before).state = SourceCurrentConjunctionSharedWorklistStep.initial budget start before := rfl

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual outcome derives its own appended credit suffix and internal certificate. -/
theorem step_frame (bound p h : Nat) (before : Frame Symbol Formula bound) :
    ∃ added, ∃ after : Frame Symbol Formula bound,
      after.state = (step p h before.state).state ∧ after.credits = before.credits ++ added := by
  obtain ⟨added, valid, bounded, budget⟩ :=
    SourceCurrentConjunctionSharedWorklistCreditBounds.step_bounded bound p h before.state
      before.valid before.bounded before.budget
  have present := SourceCurrentConjunctionSharedWorklistRefs.step_present p h before.state
    before.credits added before.present valid
  exact ⟨added, ⟨(step p h before.state).state, before.credits ++ added, valid, bounded, budget, present⟩, rfl, rfl⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistFrame
