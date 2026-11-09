import MicroCFTA.SourceCurrentConjunctionRequirementCellsNumeric
import MicroCFTA.SourceCurrentConjunctionRequirementCellsOutputBounds

/-!
# Nonincreasing profiles through actual cell forcing

Cell size bounds stored operand counts and pending job dimensions. Each
completed projection replaces one job with one collected value. Canonical
completion cannot increase the operand count. Faults retain the stopped
cursor. The measure ignores physical state and needs no heap invariants.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsSize
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Job)
open SourceCurrentConjunctionRequirementCells
open SourceCurrentConjunctionRequirementCellsNumeric (depth width)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula

/-- Stored operands and current pending dimensions determine one pure cell size. -/
def size : Cell Symbol Formula → Nat
  | .column nodes | .done nodes => nodes.length
  | .pending cursor => max (depth cursor.pending)
      (max (width cursor.pending) (cursor.collected.length + cursor.pending.length))

/-- The global profile is the maximum size of the actual stored cells. -/
def stateSize (before : Cells) : Nat :=
  before.cells.foldr (fun cell bound => max (size cell) bound) 0

private theorem member_size (cells : List (Cell Symbol Formula)) (cell : Cell Symbol Formula)
    (member : cell ∈ cells) : size cell ≤ cells.foldr (fun next bound => max (size next) bound) 0 := by
  induction cells with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- Every present handle has size at most the current global maximum. -/
theorem lookup_size (handle : Nat) (before : Cells) (cell : Cell Symbol Formula)
    (found : lookup handle before = some cell) : size cell ≤ stateSize before :=
  member_size before.cells cell (List.mem_of_getElem? found)

private theorem list_max_le (cells : List (Cell Symbol Formula)) (bound : Nat)
    (limits : ∀ cell ∈ cells, size cell ≤ bound) :
    cells.foldr (fun cell previous => max (size cell) previous) 0 ≤ bound := by
  induction cells with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact Nat.max_le.mpr ⟨limits first List.mem_cons_self,
        ih (fun cell member => limits cell (List.mem_cons_of_mem _ member))⟩

private theorem update_size (handle : Nat) (before : Cells) (original replacement : Cell Symbol Formula)
    (found : lookup handle before = some original) (smaller : size replacement ≤ size original) :
    stateSize (update handle replacement before) ≤ stateSize before := by
  apply list_max_le
  intro cell member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact member_size before.cells cell old
  · exact same.symm ▸ Nat.le_trans smaller (lookup_size handle before original found)

private theorem more_size (job : Job Symbol Formula) (rest : List (Job Symbol Formula))
    (collected : List Node) (value : Node) :
    size (.pending ⟨rest, collected ++ [value]⟩) ≤ size (.pending ⟨job :: rest, collected⟩) := by
  have depthTail : depth rest ≤ depth (job :: rest) := Nat.le_max_right _ _
  have widthTail : width rest ≤ width (job :: rest) := Nat.le_max_right _ _
  have lengths : (collected ++ [value]).length + rest.length ≤
      max (depth (job :: rest)) (max (width (job :: rest)) (collected.length + (job :: rest).length)) := by
    have old := Nat.le_trans
      (Nat.le_max_right (width (job :: rest)) (collected.length + (job :: rest).length))
      (Nat.le_max_right (depth (job :: rest)) _)
    simp only [List.length_append, List.length_cons, List.length_nil] at old ⊢
    omega
  exact Nat.max_le.mpr ⟨Nat.le_trans depthTail (Nat.le_max_left _ _),
    Nat.max_le.mpr ⟨Nat.le_trans widthTail (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)), lengths⟩⟩

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every actual cell step preserves or lowers the global size, including on faults. -/
theorem forceStep_size (p h handle : Nat) (before : Cells) :
    stateSize (forceStep p h handle before).state ≤ stateSize before := by
  cases found : lookup handle before with
  | none => simp only [forceStep, found, Outcome.state]; exact Nat.le_refl _
  | some cell =>
      cases cell with
      | done nodes => simp only [forceStep, found, Outcome.state]; exact Nat.le_refl _
      | column nodes =>
          simp only [forceStep, found, Outcome.state]
          exact update_size handle before (.column nodes) _ found
            (SourceCurrentConjunctionRequirementCellsOutputBounds.canonical_length nodes)
      | pending cursor =>
          rcases cursor with ⟨jobs, collected⟩
          cases jobs with
          | nil =>
              simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, Outcome.state]
              apply update_size handle before (.pending ⟨[], collected⟩) _ found
              simpa only [size, depth, width, List.foldr_nil, List.length_nil, Nat.add_zero, Nat.zero_max] using
                SourceCurrentConjunctionRequirementCellsOutputBounds.canonical_length collected
          | cons job rest =>
              cases projected : SourceCurrentConjunctionRequirementPull.projection p h job before.physical with
              | failed fault physical =>
                  simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, projected,
                    SourceCurrentConjunctionRowsWorker.Outcome.bind, Outcome.state]
                  exact Nat.le_refl _
              | done value physical =>
                  cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
                  | true =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, projected,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, ite_true, Outcome.state]
                      apply update_size handle {before with physical := physical} (.pending ⟨job :: rest, collected⟩) _ found
                      change 1 ≤ max (depth (job :: rest))
                        (max (width (job :: rest)) (collected.length + (job :: rest).length))
                      apply Nat.le_trans _ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
                      simp only [List.length_cons]
                      omega
                  | false =>
                      simp only [forceStep, found, SourceCurrentConjunctionRequirementPull.step, projected,
                        SourceCurrentConjunctionRowsWorker.Outcome.bind, tested, Bool.false_eq_true, ite_false, Outcome.state]
                      exact update_size handle {before with physical := physical} (.pending ⟨job :: rest, collected⟩)
                        (.pending ⟨rest, collected ++ [value]⟩) found (more_size job rest collected value)

/-- Complete forcing cannot increase the global profile on any actual outcome. -/
theorem force_size (p h handle : Nat) (before : Cells) :
    stateSize (force p h handle before).state ≤ stateSize before := by
  suffices ∀ weight (current : Cells), remaining handle current = weight →
      stateSize (force p h handle current).state ≤ stateSize current by
    exact this _ before rfl
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight smaller =>
      intro current measured
      rw [force_step]
      have first := forceStep_size p h handle current
      cases observed : forceStep p h handle current with
      | failed fault after => simpa only [observed, Outcome.state] using first
      | done event middle =>
          have bound : stateSize middle ≤ stateSize current := by
            simpa only [observed, Outcome.state] using first
          cases event with
          | complete nodes => exact bound
          | more cursor =>
              have decrease : remaining handle middle < weight := by
                rw [← measured]
                exact forceStep_more_decreases p h handle current middle cursor observed
              exact Nat.le_trans (smaller _ decrease middle rfl) bound

end MicroCFTA.SourceCurrentConjunctionRequirementCellsSize
