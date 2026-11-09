import MicroCFTA.SourceCurrentConjunctionSharedWorklistFrame
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStepProgress
import MicroCFTA.HeightOrderControlled

/-!
# Numeric coordinates for the actual shared worklist rank

The remaining budget is the highest coordinate. The lower coordinates are
the actual queue coefficients. The original budget fixes their dimension.
The current queue size bounds each coefficient. Every continuing transition
derives its next frame and a strict decrease in this finite vector.
The physical resource control function remains a separate obligation.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistNumericControl
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistFrame (Frame)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Weight" => SourceCurrentConjunctionSharedWorklistWeight.weight
local notation "Rank" => SourceCurrentConjunctionSharedWorklistWeight.rank

/-- A requirement task counts its handles and the task itself. -/
def taskSize : Task Symbol Formula → Nat
  | .nodes _ => 1
  | .requirements handles => handles.length + 1
  | .rows _ => 1

/-- The current literal queue supplies one bound for every queue coefficient. -/
def queueSize : List (Task Symbol Formula) → Nat
  | [] => 0
  | task :: rest => taskSize task + queueSize rest

/-- The current budget and queue size bound the complete packed vector. -/
def control (before : State Symbol Formula) : Nat :=
  max before.budget (queueSize before.pending)

/-- Pack the actual budget above the original fixed queue coordinates. -/
def measure (bound : Nat) (credits : List Nat) (before : State Symbol Formula) : Nat → Nat :=
  fun index => if index = bound + 2 then before.budget
    else HeightOrder.extend (Rank bound credits before.pending) index

private theorem taskWeight_le (credits : List Nat) (task : Task Symbol Formula) (index : Nat) :
    SourceCurrentConjunctionSharedWorklistWeight.taskWeight credits task index ≤ taskSize task := by
  cases task with
  | nodes values =>
      simp only [SourceCurrentConjunctionSharedWorklistWeight.taskWeight, taskSize]
      split <;> omega
  | requirements handles =>
      simp only [SourceCurrentConjunctionSharedWorklistWeight.taskWeight, taskSize]
      split <;> omega
  | rows handle =>
      cases found : credits[handle]? with
      | none =>
          simp only [SourceCurrentConjunctionSharedWorklistWeight.taskWeight, taskSize, found]
          omega
      | some credit =>
          simp only [SourceCurrentConjunctionSharedWorklistWeight.taskWeight, taskSize, found]
          split <;> omega

private theorem weight_le (credits : List Nat) (pending : List (Task Symbol Formula)) (index : Nat) :
    Weight credits pending index ≤ queueSize pending := by
  induction pending with
  | nil => exact Nat.le_refl _
  | cons task rest ih =>
      exact Nat.add_le_add (taskWeight_le credits task index) ih

/-- Every packed coordinate is bounded by current data, including coordinates outside the vector. -/
theorem measure_bound (bound : Nat) (credits : List Nat) (before : State Symbol Formula) (index : Nat) :
    measure bound credits before index ≤ control before := by
  by_cases top : index = bound + 2
  · subst index
    simp only [measure, control, ↓reduceIte]
    exact Nat.le_max_left _ _
  · simp only [measure, ite_eq_right top]
    by_cases inside : index < bound + 2
    · simp only [HeightOrder.extend, dite_eq_left inside]
      exact Nat.le_trans (weight_le credits before.pending index) (Nat.le_max_right _ _)
    · simp only [HeightOrder.extend, dite_eq_right inside]
      exact Nat.zero_le _

/-- Initialization needs only the original budget and one initial queue task. -/
theorem initial_control (budget : Nat) (start : Node)
    (before : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) :
    control (initial budget start before) = max budget 1 := by
  rfl

private theorem below_replace : ∀ (dimension : Nat) (first last nextFirst nextLast : Nat → Nat),
    (∀ index, index < dimension → nextFirst index = first index) →
    (∀ index, index < dimension → nextLast index = last index) →
    HeightOrder.Below dimension first last → HeightOrder.Below dimension nextFirst nextLast := by
  intro dimension
  induction dimension with
  | zero => intro first last nextFirst nextLast sameFirst sameLast actual; exact False.elim actual
  | succ dimension ih =>
      intro first last nextFirst nextLast sameFirst sameLast actual
      change Prod.Lex Nat.lt (HeightOrder.Below dimension)
        (first dimension, first) (last dimension, last) at actual
      change Prod.Lex Nat.lt (HeightOrder.Below dimension)
        (nextFirst dimension, nextFirst) (nextLast dimension, nextLast)
      apply Prod.lex_def.mpr
      rcases Prod.lex_def.mp actual with less | ⟨same, lower⟩
      · exact Or.inl (by simpa only [sameFirst dimension (by omega), sameLast dimension (by omega)] using less)
      · refine Or.inr ⟨(sameFirst dimension (by omega)).trans (same.trans (sameLast dimension (by omega)).symm), ?_⟩
        exact ih first last nextFirst nextLast
          (fun index inside => sameFirst index (by omega))
          (fun index inside => sameLast index (by omega)) lower

private theorem packed_below (bound : Nat) (firstCredits lastCredits : List Nat)
    (first last : State Symbol Formula)
    (actual : Prod.Lex Nat.lt (HeightOrder.VectorBelow (bound + 2))
      (first.budget, Rank bound firstCredits first.pending)
      (last.budget, Rank bound lastCredits last.pending)) :
    HeightOrder.Below (bound + 3) (measure bound firstCredits first) (measure bound lastCredits last) := by
  change Prod.Lex Nat.lt (HeightOrder.Below (bound + 2))
    (measure bound firstCredits first (bound + 2), measure bound firstCredits first)
    (measure bound lastCredits last (bound + 2), measure bound lastCredits last)
  simp only [measure]
  apply Prod.lex_def.mpr
  rcases Prod.lex_def.mp actual with less | ⟨same, lower⟩
  · exact Or.inl less
  · refine Or.inr ⟨same, ?_⟩
    apply below_replace (bound + 2)
      (HeightOrder.extend (Rank bound firstCredits first.pending))
      (HeightOrder.extend (Rank bound lastCredits last.pending))
      (measure bound firstCredits first) (measure bound lastCredits last)
    · intro index inside
      simp only [measure, ite_eq_right (show index ≠ bound + 2 by omega)]
    · intro index inside
      simp only [measure, ite_eq_right (show index ≠ bound + 2 by omega)]
    · exact lower

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- An actual continuing step derives its own next frame and packed-vector decrease. -/
theorem step_below (bound p h : Nat) (before : Frame Symbol Formula bound)
    (after : State Symbol Formula) (actual : step p h before.state = .done .more after) :
    ∃ added, ∃ next : Frame Symbol Formula bound,
      next.state = after ∧ next.credits = before.credits ++ added ∧
      HeightOrder.Below (bound + 3)
        (measure bound next.credits next.state) (measure bound before.credits before.state) := by
  obtain ⟨added, next, stateSame, creditsSame⟩ :=
    SourceCurrentConjunctionSharedWorklistFrame.step_frame bound p h before
  have nextState : next.state = after := by
    simpa only [actual, Outcome.state] using stateSame
  have post : SourceCurrentConjunctionRequirementRowsOrigins.Credits
      (before.credits ++ added) after.storage := by
    rw [← creditsSame, ← nextState]
    exact next.valid
  have decrease := SourceCurrentConjunctionSharedWorklistStepProgress.step_decreases bound p h
    before.credits added before.state after before.bounded before.present actual post
  refine ⟨added, next, nextState, creditsSame, ?_⟩
  rw [nextState, creditsSame]
  exact packed_below bound (before.credits ++ added) before.credits after before.state decrease

end MicroCFTA.SourceCurrentConjunctionSharedWorklistNumericControl
