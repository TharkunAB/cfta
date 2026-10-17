import MicroCFTA.HeightOrderControlled

/-!
# Monotone initial bounds for controlled vector descent

Increasing the dimension retains every smaller-dimensional majorant.
The dimension and initial control can therefore increase together.
-/
namespace MicroCFTA.HeightOrderControlled

private theorem iterate_retains (next : Nat → Nat) (grows : ∀ value, value ≤ next value)
    (count value : Nat) : value ≤ iterate next count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (grows value) (ih (next value))

/-- One extra dimension retains the majorant at the same initial control. -/
theorem majorant_dimension_succ (control : Nat → Nat) (grows : ∀ value, value < control value)
    (dimension value : Nat) :
    majorant control dimension value ≤ majorant control (dimension + 1) value := by
  rw [majorant_succ, iterate]
  exact Nat.le_trans (Nat.le_of_lt (grows _))
    (iterate_retains _ (fun current => Nat.le_trans (majorant_ge control grows dimension current)
      (Nat.le_of_lt (grows _))) value _)

/-- A larger dimension retains the majorant at the same initial control. -/
theorem majorant_dimension_mono (control : Nat → Nat) (grows : ∀ value, value < control value)
    {first last : Nat} (increase : first ≤ last) (value : Nat) :
    majorant control first value ≤ majorant control last value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  clear increase
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra ih => exact Nat.le_trans ih (majorant_dimension_succ control grows _ _)

/-- Larger dimensions and initial controls retain the same majorant. -/
theorem majorant_joint_mono (control : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value)
    {firstDimension lastDimension firstControl lastControl : Nat}
    (dimensions : firstDimension ≤ lastDimension) (controls : firstControl ≤ lastControl) :
    majorant control firstDimension firstControl ≤ majorant control lastDimension lastControl :=
  Nat.le_trans (majorant_mono control mono grows firstDimension controls)
    (majorant_dimension_mono control grows dimensions lastControl)

/-- One larger initial bound can increase both dimension and control. -/
theorem majorant_diagonal_mono (control : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → control first ≤ control last)
    (grows : ∀ value, value < control value)
    {first last : Nat} (increase : first ≤ last) :
    majorant control first first ≤ majorant control last last :=
  majorant_joint_mono control mono grows increase increase

end MicroCFTA.HeightOrderControlled
