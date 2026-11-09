import MicroCFTA.SourceCurrentConjunctionRequirementCells

/-!
# Stable cell allocation through actual forcing

Cell forcing replaces a descriptor at its existing handle. It does not
append or remove cells. Both successful and failed outcomes preserve the
cell count. Every previously present handle therefore remains present.
Exact other-cell framing and successful cache publication have separate laws.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsFrame
open InternedConstructorTemplates
open SourceCurrentConjunctionRequirementCells
variable {Symbol Formula : Type}
local notation "CellState" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual force step retains the cell count, including on missing handles and projection faults. -/
theorem forceStep_length (p h handle : Nat) (before : CellState) :
    (forceStep p h handle before).state.cells.length = before.cells.length := by
  cases found : lookup handle before with
  | none => simp only [forceStep, found, Outcome.state]
  | some cell =>
      cases cell with
      | done nodes => simp only [forceStep, found, Outcome.state]
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          exact update_length _ _ _
      | pending cursor =>
          cases actual : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
          | failed fault after => simp only [forceStep, found, actual, Outcome.state]
          | done event after =>
              cases event <;> simp only [forceStep, found, actual, Outcome.state] <;>
                exact update_length _ _ _

/-- Complete finite forcing retains the same cell count on every outcome. -/
theorem force_length (p h handle : Nat) (before : CellState) :
    (force p h handle before).state.cells.length = before.cells.length := by
  suffices ∀ weight (current : CellState), remaining handle current = weight →
      (force p h handle current).state.cells.length = current.cells.length by
    exact this _ before rfl
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured
      rw [force_step]
      have first := forceStep_length p h handle current
      cases actual : forceStep p h handle current with
      | failed fault after => simpa only [actual, Outcome.state] using first
      | done event after =>
          have retained : after.cells.length = current.cells.length := by
            simpa only [actual, Outcome.state] using first
          cases event with
          | complete nodes => exact retained
          | more cursor =>
              have decrease : remaining handle after < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current after cursor actual
              exact (smaller _ decrease after rfl).trans retained

/-- Every previously present cell handle still has a stored descriptor after complete forcing. -/
theorem force_present (p h target : Nat) (before : CellState) (handle : Nat) (original : Cell Symbol Formula)
    (found : lookup handle before = some original) :
    ∃ cell, lookup handle (force p h target before).state = some cell := by
  have inside : handle < (force p h target before).state.cells.length := by
    rw [force_length]
    exact (List.getElem?_eq_some_iff.mp found).1
  exact ⟨(force p h target before).state.cells[handle], List.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩

end MicroCFTA.SourceCurrentConjunctionRequirementCellsFrame
