import MicroCFTA.LatticeRank

/-!
# Cost of counted binary selection

Count cumulative-count queries in the source integer binary search. This is
an operation count. The cost of evaluating a cumulative polynomial, integer
arithmetic, and compilation is separate. No language enumeration occurs in
this search.
-/

namespace MicroCFTA.SearchCost
open LatticeRank

/-- Execute the source search and retain its number of predicate queries. -/
def measured (low high : Int) (predicate : Int → Bool) : Int × Nat :=
  if low ≥ high then (low, 0)
  else
    let middle := midpoint low high
    let result := if predicate middle then measured low middle predicate
      else measured (middle + 1) high predicate
    (result.1, result.2 + 1)
termination_by (high - low).toNat
decreasing_by
  all_goals
    have hm := midpoint_bounds low high (by omega)
    omega

/-- Cost instrumentation leaves the selected coordinate unchanged. -/
theorem measured_result (low high : Int) (predicate : Int → Bool) :
    (measured low high predicate).1 = search low high predicate := by
  rw [measured, search]
  split
  · rfl
  · dsimp only
    split
    · exact measured_result low (midpoint low high) predicate
    · exact measured_result (midpoint low high + 1) high predicate
termination_by (high - low).toNat
decreasing_by
  all_goals
    have hm := midpoint_bounds low high (by omega)
    omega

/-- Each branch at least halves the integer interval width. -/
theorem half_widths (low high : Int) (ordered : low < high) :
    (midpoint low high - low).toNat ≤ (high - low).toNat / 2 ∧
      (high - (midpoint low high + 1)).toNat ≤ (high - low).toNat / 2 := by
  unfold midpoint
  omega

/-- An interval with at most `2^bits` positions needs at most `bits` queries. -/
theorem logarithmic_queries (bits : Nat) (low high : Int) (predicate : Int → Bool)
    (width : (high - low).toNat < 2 ^ bits) :
    (measured low high predicate).2 ≤ bits := by
  induction bits generalizing low high with
  | zero =>
      have done : low ≥ high := by simp only [Nat.pow_zero] at width; omega
      simp [measured, done]
  | succ bits ih =>
      rw [measured]
      split
      · simp
      · next h =>
        have halves := half_widths low high (by omega)
        have upper : (high - low).toNat < 2 ^ bits * 2 := by
          simpa [Nat.pow_succ] using width
        have left : (midpoint low high - low).toNat < 2 ^ bits := by omega
        have right : (high - (midpoint low high + 1)).toNat < 2 ^ bits := by omega
        dsimp only
        split
        · exact Nat.succ_le_succ (ih _ _ left)
        · exact Nat.succ_le_succ (ih _ _ right)

/-- A valid cumulative-count query returns the correct section within the cost bound. -/
theorem selected_with_cost (bits : Nat) (low high : Int) (cumulative : Int → Nat)
    (rank : Nat) (ordered : low ≤ high)
    (before : cumulative (low - 1) = 0) (upper : rank < cumulative high)
    (monotone : MonotoneCount cumulative) (width : (high - low).toNat < 2 ^ bits) :
    let result := measured low high (fun value => decide (rank < cumulative value))
    cumulative (result.1 - 1) ≤ rank ∧ rank < cumulative result.1 ∧ result.2 ≤ bits := by
  dsimp only
  rw [measured_result]
  have selected :=  selected_section low high cumulative rank ordered before upper monotone
  exact ⟨selected.2.2.1, selected.2.2.2, logarithmic_queries bits low high _ width⟩

end MicroCFTA.SearchCost
