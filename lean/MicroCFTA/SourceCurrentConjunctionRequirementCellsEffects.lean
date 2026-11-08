import MicroCFTA.SourceCurrentConjunctionRequirementCells
import MicroCFTA.SourceCurrentConjunctionRequirementPullEffects

/-!
# Physical effects of shared requirement cells

Only pending job forests need resident operands. Collected values and
completed cells add no physical work. Every outcome retains readiness and
the operands of every remaining job. Updates retain all other cell handles.
These laws do not select the heap or establish returned-row semantics.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementCells
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "CellState" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Cursor" => SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula

/-- An unfinished cell needs only the forests of its actual pending jobs. -/
def CellInputs (heap : InternedConstructorTemplates.State Symbol Guard) : Cell Symbol Formula → Prop
  | .pending cursor => ∀ job ∈ cursor.pending, Values heap job.1
  | _ => True

/-- Every stored pending cell retains its current projection operands. -/
def Inputs (before : CellState) : Prop :=
  ∀ handle cell, lookup handle before = some cell → CellInputs before.physical.heap cell

private theorem cellInputs_grows {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) (cell : Cell Symbol Formula)
    (inputs : CellInputs before cell) : CellInputs after cell := by
  cases cell with
  | column nodes | done nodes => trivial
  | pending cursor =>
      intro job member value included
      exact kept.available value (inputs job member value included)

private theorem inputs_grows (before : CellState) (after : Physical Symbol Formula)
    (kept : SourceEqualityRequiredCache.Keeps before.physical.heap after.heap)
    (inputs : Inputs before) : Inputs {before with physical := after} := by
  intro handle cell found
  exact cellInputs_grows kept cell (inputs handle cell found)

private theorem update_inputs (target : Nat) (original replacement : Cell Symbol Formula)
    (before : CellState) (after : Physical Symbol Formula)
    (found : lookup target before = some original) (inputs : Inputs before)
    (kept : SourceEqualityRequiredCache.Keeps before.physical.heap after.heap)
    (own : CellInputs after.heap replacement) : Inputs (update target replacement {before with physical := after}) := by
  intro handle cell present
  by_cases same : handle = target
  · subst handle
    have inserted := lookup_update target original replacement {before with physical := after} found
    have equal : replacement = cell := Option.some.inj (inserted.symm.trans present)
    exact equal ▸ own
  · have retained : lookup handle (update target replacement {before with physical := after}) =
        lookup handle before := List.getElem?_set_ne (Ne.symm same)
    have originalInputs := inputs handle cell (retained.symm.trans present)
    exact cellInputs_grows kept cell originalInputs

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every step retains the exact value at every other handle, including on faults. -/
theorem forceStep_other (p h target : Nat) (before : CellState) (handle : Nat) (different : handle ≠ target) :
    lookup handle (forceStep p h target before).state = lookup handle before := by
  cases found : lookup target before with
  | none => simp only [forceStep, found, Outcome.state]
  | some cell =>
      cases cell with
      | done nodes => simp only [forceStep, found, Outcome.state]
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          exact List.getElem?_set_ne (Ne.symm different)
      | pending cursor =>
          cases actual : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
          | failed fault after =>
              simp only [forceStep, found, actual, Outcome.state]
              rfl
          | done event after =>
              cases event <;>
                simp only [forceStep, found, actual, Outcome.state] <;>
                exact List.getElem?_set_ne (Ne.symm different)

/-- One actual cell step preserves full physical effects and every pending job's operands. -/
theorem forceStep_effects (p h handle : Nat) (before : CellState)
    (ready : Ready before.physical) (inputs : Inputs before) :
    Effects before.physical (forceStep p h handle before).state.physical ∧
      Inputs (forceStep p h handle before).state := by
  cases found : lookup handle before with
  | none =>
      simp only [forceStep, found, Outcome.state]
      exact ⟨Effects.refl _ ready, inputs⟩
  | some cell =>
      cases cell with
      | done nodes =>
          simp only [forceStep, found, Outcome.state]
          exact ⟨Effects.refl _ ready, inputs⟩
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          have kept := Effects.refl before.physical ready
          exact ⟨kept, update_inputs handle _ _ before before.physical found inputs kept.keeps trivial⟩
      | pending cursor =>
          rcases cursor with ⟨jobs, collected⟩
          cases jobs with
          | nil =>
              simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, Outcome.state]
              have kept := Effects.refl before.physical ready
              exact ⟨kept, update_inputs handle _ _ before before.physical found inputs kept.keeps trivial⟩
          | cons job rest =>
              have first := SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job
                before.physical ready (inputs handle _ found job List.mem_cons_self)
              cases actual : SourceCurrentConjunctionRequirementPull.projection p h job before.physical with
              | failed fault after =>
                  have kept : Effects before.physical after := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                  simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                    SourceCurrentConjunctionRowsWorker.Outcome.bind, Outcome.state]
                  exact ⟨kept, inputs_grows before after kept.keeps inputs⟩
              | done value after =>
                  have kept : Effects before.physical after := by
                    simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using first
                  cases empty : SourceCurrentConjunctionRequirements.isEmpty value with
                  | true =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, ite_true, Outcome.state]
                      exact ⟨kept, update_inputs handle _ _ before after found inputs kept.keeps trivial⟩
                  | false =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, actual,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, empty, Bool.false_eq_true,
                        ite_false, Outcome.state]
                      refine ⟨kept, update_inputs handle _ _ before after found inputs kept.keeps ?_⟩
                      intro later member node included
                      exact kept.keeps.available node
                        (inputs handle _ found later (List.mem_cons_of_mem _ member) node included)

/-- Complete forcing preserves every other handle on all successful and failed outcomes. -/
theorem force_other (p h target : Nat) (before : CellState) (handle : Nat) (different : handle ≠ target) :
    lookup handle (force p h target before).state = lookup handle before := by
  suffices ∀ weight (current : CellState), remaining target current = weight →
      lookup handle (force p h target current).state = lookup handle current by
    exact this _ before rfl
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured
      rw [force_step]
      have first := forceStep_other p h target current handle different
      cases actual : forceStep p h target current with
      | failed fault after => simpa only [actual, Outcome.state] using first
      | done event after =>
          have retained : lookup handle after = lookup handle current := by
            simpa only [actual, Outcome.state] using first
          cases event with
          | complete nodes => exact retained
          | more cursor =>
              have decrease : remaining target after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h target current after cursor actual
              exact (smaller _ decrease after rfl).trans retained

/-- Complete finite forcing retains readiness and all current pending-job residency, including on faults. -/
theorem force_effects (p h handle : Nat) (before : CellState)
    (ready : Ready before.physical) (inputs : Inputs before) :
    Effects before.physical (force p h handle before).state.physical ∧ Inputs (force p h handle before).state := by
  suffices ∀ weight (current : CellState), remaining handle current = weight →
      Ready current.physical → Inputs current →
      Effects current.physical (force p h handle current).state.physical ∧
        Inputs (force p h handle current).state by
    exact this _ before rfl ready inputs
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured ready inputs
      rw [force_step]
      have first := forceStep_effects p h handle current ready inputs
      cases actual : forceStep p h handle current with
      | failed fault after => simpa only [actual, Outcome.state] using first
      | done event after =>
          have kept : Effects current.physical after.physical ∧ Inputs after := by
            simpa only [actual, Outcome.state] using first
          cases event with
          | complete nodes => exact kept
          | more cursor =>
              have decrease : remaining handle after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current after cursor actual
              obtain ⟨last, resident⟩ := smaller _ decrease after rfl kept.1.ready kept.2
              exact ⟨kept.1.trans last, resident⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsEffects
