import MicroCFTA.SourceCurrentMemoMergeResourceControl
import MicroCFTA.SourceCurrentMemoMergeDirectCost

/-!
# Numeric control for recursive Merge bodies

The formulas combine literal constructor growth, actual selection growth,
and a smaller-height call bound. Iteration uses the existing controlled
vector function. These arithmetic results have no execution premises.
-/
namespace MicroCFTA.SourceCurrentMemoMergeNumericControl
open SourceCurrentMemoMergeResourceControl (primitiveGrowth selectionGrowth)
open SourceCurrentMemoMergeDirectCost (bodyBudget)
open HeightOrderControlled (iterate)

/-- Original input mass bounds the literal list widths used by one body. -/
def width (bound : Nat) : Nat := (bound + 1) ^ 2

/-- One direct instruction pays local growth and the smaller recursive call. -/
def step (width : Nat) (child : Nat → Nat) (bound : Nat) : Nat :=
  bound + 1 + max (primitiveGrowth width bound) (max (selectionGrowth bound) (child bound))

/-- Height zero has no recursive body; each larger height pays its direct body schedule. -/
def bound : Nat → Nat → Nat
  | 0, value => value + 2
  | height + 1, value =>
      iterate (step (width value) (bound height)) (bodyBudget value) value + 1

/-- Iteration of an inflationary function retains its initial value. -/
theorem iterate_ge (next : Nat → Nat) (grows : ∀ value, value ≤ next value)
    (count value : Nat) : value ≤ iterate next count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (grows value) (ih (next value))

/-- A monotone function retains the ordering of the initial values through iteration. -/
theorem iterate_mono (next : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → next first ≤ next last) (count : Nat)
    {first last : Nat} (increase : first ≤ last) : iterate next count first ≤ iterate next count last := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (mono increase)

/-- Consecutive iteration blocks retain the exact source order. -/
theorem iterate_add (next : Nat → Nat) (first last value : Nat) :
    iterate next (first + last) value = iterate next last (iterate next first value) := by
  induction first generalizing value with
  | zero => simp only [Nat.zero_add, iterate]
  | succ first ih => simpa only [Nat.succ_add, iterate] using ih (next value)

/-- The last iteration step applies to the complete earlier prefix. -/
theorem iterate_succ_right (next : Nat → Nat) (count value : Nat) :
    iterate next (count + 1) value = next (iterate next count value) := by
  exact iterate_add next count 1 value

/-- More iterations of an inflationary function retain every earlier prefix. -/
theorem iterate_count_mono (next : Nat → Nat) (grows : ∀ value, value ≤ next value)
    {first last : Nat} (counts : first ≤ last) (value : Nat) :
    iterate next first value ≤ iterate next last value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [iterate_add]
  exact iterate_ge next grows extra _

/-- Pointwise larger steps and a larger seed retain the complete iteration. -/
theorem iterate_compare (firstStep lastStep : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → lastStep first ≤ lastStep last)
    (steps : ∀ value, firstStep value ≤ lastStep value) (count : Nat)
    {first last : Nat} (increase : first ≤ last) :
    iterate firstStep count first ≤ iterate lastStep count last := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (Nat.le_trans (steps first) (mono increase))

/-- A larger input mass retains the body list-width envelope. -/
theorem width_mono {first last : Nat} (increase : first ≤ last) : width first ≤ width last := by
  have multiplied := Nat.mul_le_mul (Nat.add_le_add_right increase 1) (Nat.add_le_add_right increase 1)
  simpa only [width, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using multiplied

/-- The list-width envelope retains the original input mass and a positive unit. -/
theorem width_ge (value : Nat) : value + 1 ≤ width value := by
  have multiplied := Nat.mul_le_mul_left (value + 1) (by omega : 1 ≤ value + 1)
  simpa only [width, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one] using multiplied

/-- A larger original input mass retains its direct body instruction budget. -/
theorem bodyBudget_mono {first last : Nat} (increase : first ≤ last) : bodyBudget first ≤ bodyBudget last := by
  have bases := Nat.add_le_add_right increase 1
  have squared := Nat.mul_le_mul bases bases
  have cubed := Nat.mul_le_mul squared bases
  have scaled := Nat.mul_le_mul_left 100 cubed
  simpa only [bodyBudget, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using scaled

/-- The direct body instruction budget retains a positive original bound. -/
theorem bodyBudget_ge (value : Nat) : value + 1 ≤ bodyBudget value := by
  have squared := width_ge value
  have cubed := Nat.mul_le_mul_left ((value + 1) ^ 2) (by omega : 1 ≤ value + 1)
  simp only [Nat.mul_one] at cubed
  have scale := Nat.mul_le_mul_right ((value + 1) ^ 3) (by decide : 1 ≤ 100)
  simp only [Nat.one_mul] at scale
  unfold width at squared
  unfold bodyBudget
  rw [← Nat.pow_succ] at cubed
  change (value + 1) ^ 2 ≤ (value + 1) ^ 3 at cubed
  omega

/-- Every local step adds at least one unit to its current scalar bound. -/
theorem step_ge (width : Nat) (child : Nat → Nat) (value : Nat) : value + 1 ≤ step width child value := by
  unfold step
  omega

/-- Each step pays the current resources, the smaller call, and one instruction. -/
theorem step_pays_child (width : Nat) (child : Nat → Nat) (value : Nat) :
    value + child value + 1 ≤ step width child value := by
  unfold step
  omega

/-- The next scalar bound covers the literal constructor growth. -/
theorem step_primitive (width : Nat) (child : Nat → Nat) (value : Nat) :
    primitiveGrowth width value ≤ step width child value := by
  unfold step
  omega

/-- The next scalar bound covers all actual selection unfolding effects. -/
theorem step_selection (width : Nat) (child : Nat → Nat) (value : Nat) :
    selectionGrowth value ≤ step width child value := by
  unfold step
  omega

/-- The next scalar bound covers the smaller recursive call. -/
theorem step_child (width : Nat) (child : Nat → Nat) (value : Nat) : child value ≤ step width child value := by
  unfold step
  omega

/-- Larger widths and child bounds retain one step at the same current scalar. -/
theorem step_compare {firstWidth lastWidth : Nat} {firstChild lastChild : Nat → Nat}
    (widths : firstWidth ≤ lastWidth) (children : ∀ value, firstChild value ≤ lastChild value) (value : Nat) :
    step firstWidth firstChild value ≤ step lastWidth lastChild value := by
  have primitive := SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono widths (Nat.le_refl value)
  have child := children value
  unfold step
  omega

/-- A monotone child bound makes each fixed-width step monotone. -/
theorem step_mono (width : Nat) (child : Nat → Nat)
    (mono : ∀ {first last}, first ≤ last → child first ≤ child last)
    {first last : Nat} (increase : first ≤ last) : step width child first ≤ step width child last := by
  have primitive := SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono (Nat.le_refl width) increase
  have selection := SourceCurrentMemoMergeResourceControl.selectionGrowth_mono increase
  have children := mono increase
  unfold step
  omega

/-- Every height bound retains the original scalar resources and two units. -/
theorem bound_ge (height value : Nat) : value + 2 ≤ bound height value := by
  cases height with
  | zero => exact Nat.le_refl _
  | succ height =>
      have counts : 1 ≤ bodyBudget value := by have known := bodyBudget_ge value; omega
      have retained := iterate_count_mono (step (width value) (bound height))
        (fun current => Nat.le_trans (Nat.le_add_right current 1) (step_ge _ _ current)) counts value
      have first := step_ge (width value) (bound height) value
      change step (width value) (bound height) value ≤ _ at retained
      simp only [bound]
      omega

/-- Larger original scalar resources retain the bound at the same ordinary height. -/
theorem bound_mono (height : Nat) {first last : Nat} (increase : first ≤ last) :
    bound height first ≤ bound height last := by
  induction height generalizing first last with
  | zero => exact Nat.add_le_add_right increase 2
  | succ height ih =>
      have compared := iterate_compare (step (width first) (bound height)) (step (width last) (bound height))
        (step_mono (width last) (bound height) (fun enough => ih enough))
        (step_compare (width_mono increase) (fun _ => Nat.le_refl _)) (bodyBudget first) increase
      have longer := iterate_count_mono (step (width last) (bound height))
        (fun current => Nat.le_trans (Nat.le_add_right current 1) (step_ge _ _ current)) (bodyBudget_mono increase) last
      exact Nat.add_le_add_right (Nat.le_trans compared longer) 1

end MicroCFTA.SourceCurrentMemoMergeNumericControl
