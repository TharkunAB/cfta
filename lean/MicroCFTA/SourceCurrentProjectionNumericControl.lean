import MicroCFTA.SourceCurrentMemoMergeNumericControl
import MicroCFTA.SourceCurrentProjectionUnionResources

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
open SourceCurrentProjectionUnionResources (headGrowth unionGrowth)

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

/-- An ordinary projection visits its original rows before the final source union. -/
def ordinary (child : Nat → Nat) (value : Nat) : Nat := unionGrowth value (rowsBound child value value)

/-- Path depth zero keeps the input; each proper step first pays a possible recursive head. -/
def bound : Nat → Nat → Nat
  | 0, value => value + 1
  | depth + 1, value => ordinary (bound depth) (headGrowth value)

/-- The final source union retains the complete earlier row-traversal scalar. -/
theorem rowsBound_le_ordinary (child : Nat → Nat) (value : Nat) : rowsBound child value value ≤ ordinary child value :=
  SourceCurrentProjectionUnionResources.unionGrowth_ge value _

/-- An ordinary projection retains its initial resources. -/
theorem ordinary_ge (child : Nat → Nat) (value : Nat) : value ≤ ordinary child value :=
  Nat.le_trans (rowsBound_ge child value value) (rowsBound_le_ordinary child value)

/-- Larger children and an initial scalar retain the complete ordinary projection envelope. -/
theorem ordinary_compare {firstChild lastChild : Nat → Nat}
    (mono : ∀ {first last}, first ≤ last → lastChild first ≤ lastChild last)
    (children : ∀ value, firstChild value ≤ lastChild value)
    {first last : Nat} (increase : first ≤ last) : ordinary firstChild first ≤ ordinary lastChild last :=
  SourceCurrentProjectionUnionResources.unionGrowth_mono increase
    (rowsBound_compare mono children increase increase)

/-- A monotone child makes the ordinary projection envelope monotone. -/
theorem ordinary_mono (child : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → child first ≤ child last)
    {first last : Nat} (increase : first ≤ last) : ordinary child first ≤ ordinary child last :=
  ordinary_compare mono (fun _ => Nat.le_refl _) increase

/-- The complete path envelope retains its initial scalar at every depth. -/
theorem bound_ge (depth value : Nat) : value ≤ bound depth value := by
  cases depth with
  | zero => exact Nat.le_succ value
  | succ depth =>
      exact Nat.le_trans (SourceCurrentProjectionUnionResources.headGrowth_ge value)
        (ordinary_ge (bound depth) (headGrowth value))

/-- A larger initial scalar retains the complete envelope at the same path depth. -/
theorem bound_mono (depth : Nat) {first last : Nat} (increase : first ≤ last) : bound depth first ≤ bound depth last := by
  induction depth generalizing first last with
  | zero => exact Nat.add_le_add_right increase 1
  | succ depth ih =>
      exact ordinary_mono (bound depth) (fun enough => ih enough)
        (SourceCurrentProjectionUnionResources.headGrowth_mono increase)

/-- The head branch and its following ordinary branch use the same complete envelope. -/
theorem head_ordinary_eq (depth value : Nat) :
    ordinary (bound depth) (headGrowth value) = bound (depth + 1) value := rfl

/-- A direct ordinary branch fits the envelope that also permits one recursive head. -/
theorem ordinary_le_bound (depth value : Nat) : ordinary (bound depth) value ≤ bound (depth + 1) value :=
  ordinary_mono (bound depth) (fun enough => bound_mono depth enough)
    (SourceCurrentProjectionUnionResources.headGrowth_ge value)

/-- The possible recursive head retains its exact reached scalar before row traversal. -/
theorem headGrowth_le_bound (depth value : Nat) : headGrowth value ≤ bound (depth + 1) value :=
  ordinary_ge (bound depth) (headGrowth value)

/-- Direct ordinary rows fit the complete path envelope before its final union. -/
theorem rowsBound_le_bound (depth value : Nat) : rowsBound (bound depth) value value ≤ bound (depth + 1) value :=
  Nat.le_trans (rowsBound_le_ordinary (bound depth) value) (ordinary_le_bound depth value)

/-- Rows after a recursive head fit the same path envelope before their final union. -/
theorem rowsBound_head_le_bound (depth value : Nat) :
    rowsBound (bound depth) (headGrowth value) (headGrowth value) ≤ bound (depth + 1) value :=
  rowsBound_le_ordinary (bound depth) (headGrowth value)

/-- A positive original scalar lets an ordinary envelope pay its first child. -/
theorem child_le_ordinary (child : Nat → Nat) {value : Nat} (positive : 0 < value) : child value ≤ ordinary child value :=
  Nat.le_trans (child_le_rowsBound child positive) (rowsBound_le_ordinary child value)

/-- The complete path envelope covers a first direct child at a positive initial scalar. -/
theorem child_le_bound (depth : Nat) {value : Nat} (positive : 0 < value) : bound depth value ≤ bound (depth + 1) value :=
  Nat.le_trans (child_le_ordinary (bound depth) positive) (ordinary_le_bound depth value)

end MicroCFTA.SourceCurrentProjectionNumericControl
