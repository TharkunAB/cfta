import MicroCFTA.SourceCurrentConstrainedCapTargetForecast
import MicroCFTA.HeightOrderControlledMonotone

/-!
# Monotone initial Target forecasts

Larger initial profiles retain every scheduled Operand, Fold, and query
bound. Reservations for the larger schedule supply the smaller schedule.
All comparisons are pure arithmetic and require no completed execution.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapTargetMonotone
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapTargetForecast
namespace Merge
export SourceCurrentMemoMergeNumericControl (bound step width bound_ge bound_mono
  iterate_compare step_compare step_mono)
export SourceCurrentMemoMergeDirectCost (bodyBudget)
end Merge

private theorem mergeBound_step (height value : Nat) : Merge.bound height value ≤ Merge.bound (height + 1) value := by
  induction height generalizing value with
  | zero => exact Merge.bound_ge 1 value
  | succ height ih =>
      exact Nat.add_le_add_right
        (Merge.iterate_compare _ _ (Merge.step_mono _ _ (fun increase => Merge.bound_mono _ increase))
          (Merge.step_compare (Nat.le_refl _) (fun value => ih value))
          (Merge.bodyBudget value) (Nat.le_refl value)) 1

/-- A larger ordinary height retains the same initial scalar Merge bound. -/
theorem mergeBound_height_mono {first last : Nat} (increase : first ≤ last) (value : Nat) :
    Merge.bound first value ≤ Merge.bound last value := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increase
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra ih => exact Nat.le_trans ih (mergeBound_step (first + extra) value)

/-- Larger initial resources retain the scalar-only Merge work fuel. -/
theorem mergeWorkFuel_mono {first last : Nat} (increase : first ≤ last) :
    SourceCurrentMemoMergeUniformNumeric.workFuel first ≤ SourceCurrentMemoMergeUniformNumeric.workFuel last :=
  Nat.le_trans (mergeBound_height_mono increase first) (Merge.bound_mono last increase)

private theorem comparisonFuel_mono {first last : Nat} (increase : first ≤ last) :
    SourceMergedComparisonNumeric.comparisonFuel first first first ≤
      SourceMergedComparisonNumeric.comparisonFuel last last last := by
  have heaps := SourceCurrentMemoMergeResourceControl.selectionGrowth_mono increase
  have rows := SourceCurrentProjectionUnionResources.readFuel_mono heaps
  have pairs := Nat.mul_le_mul heaps heaps
  change SourceCurrentAllocatedUnfoldHistory.heapBound first first first ≤
    SourceCurrentAllocatedUnfoldHistory.heapBound last last last at heaps
  change SourceCurrentAllocatedRowReadNumeric.readFuel
      (SourceCurrentAllocatedUnfoldHistory.heapBound first first first)
      (SourceCurrentAllocatedUnfoldHistory.heapBound first first first)
      (SourceCurrentAllocatedUnfoldHistory.heapBound first first first) ≤
    SourceCurrentAllocatedRowReadNumeric.readFuel
      (SourceCurrentAllocatedUnfoldHistory.heapBound last last last)
      (SourceCurrentAllocatedUnfoldHistory.heapBound last last last)
      (SourceCurrentAllocatedUnfoldHistory.heapBound last last last) at rows
  unfold SourceMergedComparisonNumeric.comparisonFuel SourceMergedComparisonNumeric.readerFuel
  exact Nat.add_le_add (Nat.add_le_add_left pairs 1) rows

/-- Larger initial resources retain every nested Merge selection allowance. -/
theorem mergeSelectionFuel_mono {first last : Nat} (increase : first ≤ last) :
    SourceCurrentMemoMergeUniformNumeric.selectionFuel first ≤ SourceCurrentMemoMergeUniformNumeric.selectionFuel last :=
  comparisonFuel_mono (mergeWorkFuel_mono increase)

private theorem projectionBound_mono (path : List Int) (count : Nat) {first last : Nat} (increase : first ≤ last) :
    SourceCurrentConstrainedCapOperandNumeric.projectionBound path count first ≤
      SourceCurrentConstrainedCapOperandNumeric.projectionBound path count last := by
  cases path with
  | nil => exact SourceCurrentProjectionUnionResources.unionGrowth_mono (Nat.le_refl count) increase
  | cons index path => exact SourceCurrentProjectionNumericControl.bound_mono path.length increase

private theorem operandWork_mono (path : List Int) (count : Nat) {first last : Nat} (increase : first ≤ last) :
    SourceCurrentConstrainedCapOperandNumeric.workFuel path count first ≤
      SourceCurrentConstrainedCapOperandNumeric.workFuel path count last :=
  mergeWorkFuel_mono (projectionBound_mono path count increase)

private theorem operandSelection_mono (path : List Int) (count : Nat) {first last : Nat} (increase : first ≤ last) :
    SourceCurrentConstrainedCapOperandNumeric.selectionFuel path count first ≤
      SourceCurrentConstrainedCapOperandNumeric.selectionFuel path count last :=
  mergeSelectionFuel_mono (projectionBound_mono path count increase)

private theorem operandRead_mono (path : List Int) (count : Nat) {first last : Nat} (increase : first ≤ last) :
    SourceCurrentProjectionNumeric.readFuel path count first ≤ SourceCurrentProjectionNumeric.readFuel path count last :=
  SourceCurrentProjectionUnionResources.readFuel_mono (projectionBound_mono path count increase)

/-- Larger initial components retain the complete selected Operand profile. -/
theorem operand_mono (path : List Int) (count : Nat) {first last : Profile} (increase : Le first last) :
    Le (operand path count first) (operand path count last) := by
  have work := operandWork_mono path count (scalar_mono increase)
  exact ⟨work, work, increase.2.2.1, work⟩

/-- Larger initial components retain the exact head-tail-query Fold profile. -/
theorem foldProfile_mono (count : Nat) (seed : List Int) (paths : List (List Int))
    {first last : Profile} (increase : Le first last) :
    Le (foldProfile count seed paths first) (foldProfile count seed paths last) := by
  induction paths generalizing first last with
  | nil => exact operand_mono seed count increase
  | cons path paths ih =>
      exact SourceCurrentAllocatedNativeResourceForecast.step_mono (ih (operand_mono path count increase))

/-- Larger initial components retain the whole Target profile, including its empty case. -/
theorem targetProfile_mono (count : Nat) (paths : List (List Int)) {first last : Profile} (increase : Le first last) :
    Le (targetProfile count paths first) (targetProfile count paths last) := by
  cases paths with
  | nil => exact increase
  | cons seed paths => exact foldProfile_mono count seed paths increase

/-- Reservations for a larger initial Fold profile supply every smaller reached query entry. -/
theorem reserved_mono (bits count : Nat) (seed : List Int) (paths : List (List Int))
    {first last : Profile} (increase : Le first last) (reserved : Reserved bits count seed paths last) :
    Reserved bits count seed paths first := by
  induction paths generalizing first last with
  | nil => trivial
  | cons path paths ih =>
      have head := operand_mono path count increase
      exact ⟨ih head reserved.1, reserved.2.mono (foldProfile_mono count seed paths head)⟩

/-- A larger initial Target reservation also supplies the smaller initial profile. -/
theorem targetReserved_mono (bits count : Nat) (paths : List (List Int)) {first last : Profile}
    (increase : Le first last) (reserved : TargetReserved bits count paths last) : TargetReserved bits count paths first := by
  cases paths with
  | nil => trivial
  | cons seed paths => exact reserved_mono bits count seed paths increase reserved

/-- Larger initial components retain the common four-fuel Operand ceiling. -/
theorem operandFuel_mono (path : List Int) (count : Nat) {first last : Profile} (increase : Le first last) :
    operandFuel path count first ≤ operandFuel path count last := by
  have scalars := scalar_mono increase
  have reads := operandRead_mono path count scalars
  have work := operandWork_mono path count scalars
  have selections := operandSelection_mono path count scalars
  unfold operandFuel
  omega

/-- Larger counters and payload mass retain the complete native query ceiling. -/
theorem queryFuel_mono {first last : Profile} (increase : Le first last) : queryFuel first ≤ queryFuel last :=
  Nat.add_le_add_right (SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono
    increase.1 increase.2.1 increase.2.2.2) 1

/-- Larger initial components retain all five Fold fuel parameters. -/
theorem foldFuel_mono (count : Nat) (seed : List Int) (paths : List (List Int))
    {first last : Profile} (increase : Le first last) : foldFuel count seed paths first ≤ foldFuel count seed paths last := by
  induction paths generalizing first last with
  | nil => exact operandFuel_mono seed count increase
  | cons path paths ih =>
      have head := operandFuel_mono path count increase
      have profiles := operand_mono path count increase
      have tail := ih profiles
      have query := queryFuel_mono (foldProfile_mono count seed paths profiles)
      simp only [foldFuel]
      omega

/-- Larger initial components retain the complete Target fuel ceiling. -/
theorem targetFuel_mono (count : Nat) (paths : List (List Int)) {first last : Profile} (increase : Le first last) :
    targetFuel count paths first ≤ targetFuel count paths last := by
  cases paths with
  | nil => exact Nat.le_refl _
  | cons seed paths => exact foldFuel_mono count seed paths increase

end MicroCFTA.SourceCurrentConstrainedCapTargetMonotone
