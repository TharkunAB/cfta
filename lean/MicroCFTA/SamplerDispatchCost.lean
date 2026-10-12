import MicroCFTA.Sampler
import MicroCFTA.DecoderDispatchCost

/-!
# Comparison cost of the source weighted-ticket lookup

The source searches group starts with the upper midpoint. The cost depends
on the number of distinct ticket widths, not the number of tickets.
-/
namespace MicroCFTA.SamplerDispatchCost
open Sampler DecoderDispatchCost

/-- Execute the source upper-midpoint search and count ticket comparisons. -/
def measured (lower : Nat → Nat) (ticket low high : Nat) : Nat × Nat :=
  if low < high then
    let middle := upperMidpoint low high
    let found := if ticket < lower middle then measured lower ticket low (middle - 1)
      else measured lower ticket middle high
    (found.1, found.2 + 1)
  else (low, 0)
termination_by high - low
decreasing_by
  all_goals
    have bounds := upperMidpoint_bounds low high (by assumption)
    omega

/-- The measured worker returns exactly the source group index. -/
theorem measured_result (lower : Nat → Nat) (ticket low high : Nat) :
    (measured lower ticket low high).1 = ticketSearch lower ticket low high := by
  rw [measured, ticketSearch]
  by_cases split : low < high
  · simp only [split, Nat.not_le.mpr split, ↓reduceIte]
    by_cases left : ticket < lower (upperMidpoint low high)
    · simp only [left, ↓reduceIte]
      exact measured_result lower ticket low (upperMidpoint low high - 1)
    · simp only [left, ↓reduceIte]
      exact measured_result lower ticket (upperMidpoint low high) high
  · simp [split]
termination_by high - low
decreasing_by
  all_goals
    have bounds := upperMidpoint_bounds low high (by assumption)
    omega

/-- Both concrete search intervals contain at most half the next power-of-two bound. -/
theorem halves (low high bits : Nat) (split : low < high)
    (bounded : high - low + 1 ≤ 2 ^ (bits + 1)) :
    (upperMidpoint low high - 1) - low + 1 ≤ 2 ^ bits ∧
      high - upperMidpoint low high + 1 ≤ 2 ^ bits := by
  have bounds := upperMidpoint_bounds low high split
  have size : high - low + 1 ≤ 2 ^ bits * 2 := by simpa [Nat.pow_succ] using bounded
  unfold upperMidpoint at *
  omega

/-- Every actual lookup takes logarithmically many ticket comparisons. -/
theorem measured_bound (lower : Nat → Nat) (ticket low high bits : Nat)
    (ordered : low ≤ high) (bounded : high - low + 1 ≤ 2 ^ bits) :
    (measured lower ticket low high).2 ≤ bits := by
  induction bits generalizing low high with
  | zero =>
      have same : low = high := by simp at bounded; omega
      subst high
      simp [measured]
  | succ bits ih =>
      by_cases split : low < high
      · have bounds := upperMidpoint_bounds low high split
        have half := halves low high bits split bounded
        rw [measured]
        simp only [split, ↓reduceIte]
        by_cases left : ticket < lower (upperMidpoint low high)
        · simp only [left, ↓reduceIte]
          exact Nat.succ_le_succ (ih low (upperMidpoint low high - 1) (by omega) half.1)
        · simp only [left, ↓reduceIte]
          exact Nat.succ_le_succ (ih (upperMidpoint low high) high bounds.2 half.2)
      · simp [measured, split]

/-- A nonempty compiled group table needs at most ceil(log2 group-count) comparisons. -/
theorem group_comparisons (groups : List (Group Value)) (ticket : Nat) (nonempty : groups ≠ []) :
    (measured (lowerBound groups) ticket 0 (groups.length - 1)).2 ≤ ceilLog2 groups.length := by
  apply measured_bound
  · omega
  · have positive := List.length_pos_iff.mpr nonempty
    have power := ceilLog2_covers groups.length
    omega

/-- The checked compiler creates a nonempty table and the logarithmic lookup bound. -/
theorem compiled_comparisons (maximum : Nat) (weighted : List (Nat × Value)) (compiled : Compiled Value)
    (found : compileWeighted maximum weighted = some compiled) (ticket : Nat) :
    (measured (lowerBound compiled.groups) ticket 0 (compiled.groups.length - 1)).2 ≤
      ceilLog2 compiled.groups.length := by
  have correct := compileWeighted_correct maximum weighted compiled found
  apply group_comparisons
  intro empty
  have total := groupWeighted_total weighted
  rw [← correct.2.1, empty] at total
  simp only [groupTotal] at total
  omega

end MicroCFTA.SamplerDispatchCost
