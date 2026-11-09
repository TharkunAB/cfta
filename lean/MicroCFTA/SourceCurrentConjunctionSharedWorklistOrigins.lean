import MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
import MicroCFTA.SourceCurrentConjunctionRequirementRowsOrigins

/-!
# Spine credits through actual shared worklist transitions

Initialization derives empty credits. Each actual visit and task transition
retains existing credits and derives any appended credits from raw lengths.
Sampling and requirement forcing change no spine cell. Row preparation uses
the checked finite raw-list induction, including failed outcomes. These laws
do not prove whole-worklist termination or select the shared executor.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistOrigins
open InternedConstructorTemplates
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
variable {Symbol Formula : Type}
local notation "Node" => Value Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula

/-- The actual initial queue and table start with an empty spine-credit list. -/
theorem initial_credits (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Credits [] (SourceCurrentConjunctionSharedWorklistStep.initial budget start before).storage :=
  SourceCurrentConjunctionRequirementRowsOrigins.initial before

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit derives its appended spine credits, including sampling faults. -/
theorem visit_credits (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) {credits : List Nat} (valid : Credits credits before.storage) :
    ∃ added, Credits (credits ++ added) (visit h nodes rest before).state.storage := by
  unfold visit
  split
  · refine ⟨[], ?_⟩
    simpa only [List.append_nil, Outcome.state] using valid
  · split
    · refine ⟨[], ?_⟩
      simpa only [List.append_nil, Outcome.state] using valid
    · cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
          before.storage.requirements.physical with
      | failed fault physical =>
          refine ⟨[], ?_⟩
          simp only [List.append_nil, Outcome.state]
          exact SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
      | done result physical =>
          cases result with
          | overflow tuples cursor =>
              refine ⟨[], ?_⟩
              simp only [List.append_nil, Outcome.state]
              exact SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
          | fit tuples =>
              cases tuples with
              | nil =>
                  refine ⟨[], ?_⟩
                  simp only [List.append_nil, Outcome.state]
                  exact SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
              | cons tuple tuples =>
                  refine ⟨[(tuple :: tuples).length], ?_⟩
                  change Credits (credits ++ [(tuple :: tuples).length])
                    (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending (tuple :: tuples))
                      (withPhysical before physical).storage).2
                  have exposed : Credits credits (withPhysical before physical).storage :=
                    SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
                  exact SourceCurrentConjunctionRequirementRowsOrigins.allocate_pending
                    exposed _

/-- Every actual task outcome derives an appended credit suffix at its exact state. -/
theorem step_credits (p h : Nat) (before : WorkState) {credits : List Nat}
    (valid : Credits credits before.storage) :
    ∃ added, Credits (credits ++ added) (step p h before).state.storage := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      refine ⟨[], ?_⟩
      simpa only [List.append_nil, Outcome.state] using valid
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_credits h nodes rest before valid
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              refine ⟨[], ?_⟩
              simpa only [List.append_nil, Outcome.state] using valid
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  refine ⟨[], ?_⟩
                  simp only [List.append_nil, Outcome.state]
                  exact SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_credits h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    (SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl)
      | rows handle =>
          obtain ⟨added, post⟩ :=
            SourceCurrentConjunctionRequirementRowsOrigins.nextRow_credits handle valid
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [advanced] at post
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨added, post⟩
          | done row storage =>
              rw [advanced] at post
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨added, post⟩
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact ⟨added, post⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistOrigins
