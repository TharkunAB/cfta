import MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
import MicroCFTA.SourceCurrentConjunctionRequirementRowsCreditBounds

/-!
# Original credit and budget bounds through shared work

The actual initial budget bounds both the remaining budget and every spine
credit. A fitting positive sample derives its credit from the actual raw
tuple count. Row transitions derive bounded tail credits from the old head.
All other outcomes retain the same spine credits. These bounds do not add
an execution allowance or prove whole-worklist termination.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistCreditBounds
open InternedConstructorTemplates
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionRequirementRowsOrigins (Credits)
variable {Symbol Formula : Type}
local notation "Node" => Value Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula

/-- The actual initial budget bounds its empty credit list and remaining budget. -/
theorem initial_bounded (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    Credits [] (SourceCurrentConjunctionSharedWorklistStep.initial budget start before).storage ∧
      (∀ credit ∈ ([] : List Nat), credit ≤ budget) ∧
      (SourceCurrentConjunctionSharedWorklistStep.initial budget start before).budget ≤ budget := by
  obtain ⟨valid, bounded⟩ := SourceCurrentConjunctionRequirementRowsCreditBounds.initial budget before
  exact ⟨valid, bounded, Nat.le_refl _⟩

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual visit derives bounded credits and retains the original budget bound. -/
theorem visit_bounded (bound h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) {credits : List Nat} (valid : Credits credits before.storage)
    (bounded : ∀ credit ∈ credits, credit ≤ bound) (budget : before.budget ≤ bound) :
    ∃ added, Credits (credits ++ added) (visit h nodes rest before).state.storage ∧
      (∀ credit ∈ credits ++ added, credit ≤ bound) ∧
      (visit h nodes rest before).state.budget ≤ bound := by
  unfold visit
  split
  · refine ⟨[], ?_⟩
    simpa only [List.append_nil, Outcome.state] using And.intro valid (And.intro bounded budget)
  · split
    · refine ⟨[], ?_⟩
      simpa only [List.append_nil, Outcome.state] using And.intro valid (And.intro bounded budget)
    · cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
          before.storage.requirements.physical with
      | failed fault physical =>
          refine ⟨[], ?_⟩
          simp only [List.append_nil, Outcome.state]
          exact ⟨SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl, bounded, budget⟩
      | done result physical =>
          cases result with
          | overflow tuples cursor =>
              refine ⟨[], ?_⟩
              simp only [List.append_nil, Outcome.state]
              exact ⟨SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl,
                bounded, Nat.zero_le _⟩
          | fit tuples =>
              cases tuples with
              | nil =>
                  refine ⟨[], ?_⟩
                  simp only [List.append_nil, Outcome.state]
                  exact ⟨SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl, bounded, budget⟩
              | cons tuple tuples =>
                  have fits := SourceCurrentConjunctionTuplePullTotal.sample_bounded h before.budget nodes
                    before.storage.requirements.physical physical (.fit (tuple :: tuples)) sampled
                  change (tuple :: tuples).length ≤ before.budget at fits
                  have enough : (tuple :: tuples).length ≤ bound := Nat.le_trans fits budget
                  have exposed : Credits credits (withPhysical before physical).storage :=
                    SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl
                  obtain ⟨allocated, allBounded⟩ :=
                    SourceCurrentConjunctionRequirementRowsCreditBounds.allocate_pending bound
                      exposed bounded (tuple :: tuples) enough
                  refine ⟨[(tuple :: tuples).length], ?_⟩
                  change Credits (credits ++ [(tuple :: tuples).length])
                    (SourceCurrentConjunctionRequirementRows.allocateSpine (.pending (tuple :: tuples))
                      (withPhysical before physical).storage).2 ∧
                    (∀ credit ∈ credits ++ [(tuple :: tuples).length], credit ≤ bound) ∧
                    before.budget - (tuples.length + 1) ≤ bound
                  exact ⟨allocated, allBounded, by omega⟩

/-- Every actual task outcome derives bounded credits at its exact reached state. -/
theorem step_bounded (bound p h : Nat) (before : WorkState) {credits : List Nat}
    (valid : Credits credits before.storage) (bounded : ∀ credit ∈ credits, credit ≤ bound)
    (budget : before.budget ≤ bound) :
    ∃ added, Credits (credits ++ added) (step p h before).state.storage ∧
      (∀ credit ∈ credits ++ added, credit ≤ bound) ∧
      (step p h before).state.budget ≤ bound := by
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending]
      refine ⟨[], ?_⟩
      simpa only [List.append_nil, Outcome.state] using And.intro valid (And.intro bounded budget)
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending]
          exact visit_bounded bound h nodes rest before valid bounded budget
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending]
              refine ⟨[], ?_⟩
              simpa only [List.append_nil, Outcome.state] using And.intro valid (And.intro bounded budget)
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle
                  before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced]
                  refine ⟨[], ?_⟩
                  simp only [List.append_nil, Outcome.state]
                  exact ⟨SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl,
                    bounded, budget⟩
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced]
                  exact visit_bounded bound h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                    (SourceCurrentConjunctionRequirementRowsOrigins.same_spines valid rfl) bounded budget
      | rows handle =>
          obtain ⟨added, post, allBounded⟩ :=
            SourceCurrentConjunctionRequirementRowsCreditBounds.nextRow_bounded bound handle valid bounded
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [advanced] at post
              rw [step_rows_failed p h handle before rest fault storage pending advanced]
              exact ⟨added, post, allBounded, budget⟩
          | done row storage =>
              rw [advanced] at post
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced]
                  exact ⟨added, post, allBounded, budget⟩
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced]
                  exact ⟨added, post, allBounded, budget⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorklistCreditBounds
