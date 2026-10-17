import MicroCFTA.SourceCurrentMemoMergeNumericControl

/-!
# Numeric control for selected path projection

Rows retain their original count while each selected child updates the
current heap bound. The complete projection recurrence also pays the
actual recursive head and the final source union.
-/
namespace MicroCFTA.SourceCurrentProjectionNumericControl
open HeightOrderControlled (iterate)
open SourceCurrentMemoMergeNumericControl
  (iterate_ge iterate_mono iterate_count_mono iterate_compare iterate_add iterate_succ_right)

/-- One selected row pays the current resources, its child projection, and one unit. -/
def rowsStep (child : Nat → Nat) (value : Nat) : Nat := value + 1 + child value

/-- Visit at most the original row count at the exact successive scalar bounds. -/
def rowsBound (child : Nat → Nat) (count value : Nat) : Nat := iterate (rowsStep child) count value

/-- Every selected row retains the current bound and adds a unit. -/
theorem rowsStep_ge (child : Nat → Nat) (value : Nat) : value + 1 ≤ rowsStep child value := by
  unfold rowsStep
  omega

/-- Every selected row pays its recursive child at the same current scalar. -/
theorem rowsStep_child (child : Nat → Nat) (value : Nat) : child value ≤ rowsStep child value := by
  unfold rowsStep
  omega

/-- The complete child charge includes the current scalar and the sequencing unit. -/
theorem rowsStep_pays_child (child : Nat → Nat) (value : Nat) :
    value + child value + 1 ≤ rowsStep child value := by
  unfold rowsStep
  omega

/-- Larger child bounds retain a single row step. -/
theorem rowsStep_compare {first last : Nat → Nat} (children : ∀ value, first value ≤ last value) (value : Nat) :
    rowsStep first value ≤ rowsStep last value := by
  have same := children value
  unfold rowsStep
  omega

/-- A monotone child makes the row step monotone in its current scalar. -/
theorem rowsStep_mono (child : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → child first ≤ child last)
    {first last : Nat} (increase : first ≤ last) : rowsStep child first ≤ rowsStep child last := by
  have same := mono increase
  unfold rowsStep
  omega

/-- An empty row traversal retains its exact initial scalar. -/
theorem rowsBound_zero (child : Nat → Nat) (value : Nat) : rowsBound child 0 value = value := rfl

/-- One more row applies its step after the complete earlier traversal. -/
theorem rowsBound_succ (child : Nat → Nat) (count value : Nat) :
    rowsBound child (count + 1) value = rowsStep child (rowsBound child count value) :=
  iterate_succ_right _ count value

/-- A first selected row precedes the remaining ordered row traversal. -/
theorem rowsBound_first (child : Nat → Nat) (count value : Nat) :
    rowsBound child (count + 1) value = rowsBound child count (rowsStep child value) := rfl

/-- Two consecutive row lists retain the same intermediate scalar. -/
theorem rowsBound_add (child : Nat → Nat) (first last value : Nat) :
    rowsBound child (first + last) value = rowsBound child last (rowsBound child first value) :=
  iterate_add _ first last value

/-- Row traversal retains its initial scalar. -/
theorem rowsBound_ge (child : Nat → Nat) (count value : Nat) : value ≤ rowsBound child count value :=
  iterate_ge _ (fun current => Nat.le_trans (Nat.le_succ current) (rowsStep_ge child current)) count value

/-- Each traversed row pays one count unit as well as its child resources. -/
theorem rowsBound_paid (child : Nat → Nat) (count value : Nat) : value + count ≤ rowsBound child count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      have tail := ih (rowsStep child value)
      have first := rowsStep_ge child value
      rw [rowsBound_first]
      omega

/-- More original rows retain every shorter traversal. -/
theorem rowsBound_count_mono (child : Nat → Nat) {first last : Nat} (counts : first ≤ last) (value : Nat) :
    rowsBound child first value ≤ rowsBound child last value :=
  iterate_count_mono _ (fun current => Nat.le_trans (Nat.le_succ current) (rowsStep_ge child current)) counts value

/-- A larger initial scalar retains the complete row traversal. -/
theorem rowsBound_mono (child : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → child first ≤ child last) (count : Nat)
    {first last : Nat} (increase : first ≤ last) : rowsBound child count first ≤ rowsBound child count last :=
  iterate_mono _ (rowsStep_mono child mono) count increase

/-- Larger child bounds, original row counts, and initial scalars retain the traversal. -/
theorem rowsBound_compare {firstChild lastChild : Nat → Nat}
    (mono : ∀ {first last}, first ≤ last → lastChild first ≤ lastChild last)
    (children : ∀ value, firstChild value ≤ lastChild value)
    {firstCount lastCount first last : Nat} (counts : firstCount ≤ lastCount) (increase : first ≤ last) :
    rowsBound firstChild firstCount first ≤ rowsBound lastChild lastCount last :=
  Nat.le_trans (iterate_compare _ _ (rowsStep_mono lastChild mono) (rowsStep_compare children) firstCount increase)
    (rowsBound_count_mono lastChild counts last)

/-- Any nonempty traversal covers its first child at the initial scalar. -/
theorem child_le_rowsBound (child : Nat → Nat) {count value : Nat} (positive : 0 < count) :
    child value ≤ rowsBound child count value :=
  Nat.le_trans (rowsStep_child child value)
    (rowsBound_count_mono child (by omega : 1 ≤ count) value)

end MicroCFTA.SourceCurrentProjectionNumericControl
