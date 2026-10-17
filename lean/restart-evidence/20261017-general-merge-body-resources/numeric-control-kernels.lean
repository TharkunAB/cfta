import MicroCFTA.SourceCurrentMemoMergeNumericControl

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MergeNumericControlIntegration
open SourceCurrentMemoMergeNumericControl
open SourceCurrentMemoMergeDirectCost (bodyBudget)
open HeightOrderControlled (iterate)

/-- Small concrete envelopes retain the literal width, direct cost, and local child charge. -/
theorem evaluated_envelopes :
    width 0 = 1 ∧ width 3 = 16 ∧ bodyBudget 0 = 100 ∧ bodyBudget 2 = 2700 ∧
      bound 0 5 = 7 ∧ step 1 (fun value => value + 2) 0 = 3 := by decide

/-- Two completed instruction blocks and one bind use the exact reached intermediate scalars. -/
theorem evaluated_bind_schedule :
    iterate (fun value => 2 * value + 1) 3 2 = 23 ∧
    iterate (fun value => 2 * value + 1) 2 23 = 95 ∧
    iterate (fun value => 2 * value + 1) (3 + 2 + 1) 2 = 191 ∧
    iterate (fun value => 2 * value + 1) (3 + 2 + 1) 2 =
      (fun value => 2 * value + 1)
        (iterate (fun value => 2 * value + 1) 2 (iterate (fun value => 2 * value + 1) 3 2)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [iterate_succ_right, iterate_add]

private theorem elapsed (next : Nat → Nat) (paid : ∀ value, value + 1 ≤ next value)
    (count value : Nat) : value + count ≤ iterate next count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih =>
      have rest := ih (next value)
      have first := paid value
      change value + (count + 1) ≤ iterate next count (next value)
      omega

/-- A shorter local schedule fits the original height envelope even when its initial scalar increases. -/
theorem shorter_schedule_in_larger_initial_bound (height first last count : Nat)
    (increase : first ≤ last) (shorter : count ≤ bodyBudget first) :
    first + count ≤ iterate (step (width first) (bound height)) count first ∧
      iterate (step (width first) (bound height)) count first + 1 ≤ bound (height + 1) last := by
  have compared := iterate_compare (step (width first) (bound height)) (step (width last) (bound height))
    (step_mono (width last) (bound height) (fun enough => bound_mono height enough))
    (step_compare (width_mono increase) (fun _ => Nat.le_refl _)) count increase
  have retained := iterate_count_mono (step (width last) (bound height))
    (fun value => Nat.le_trans (Nat.le_succ value) (step_ge _ _ value))
    (Nat.le_trans shorter (bodyBudget_mono increase)) last
  exact ⟨elapsed _ (step_ge _ _) count first,
    Nat.add_le_add_right (Nat.le_trans compared retained) 1⟩

#print axioms evaluated_envelopes
#check @evaluated_envelopes
#print axioms evaluated_bind_schedule
#check @evaluated_bind_schedule
#print axioms shorter_schedule_in_larger_initial_bound
#check @shorter_schedule_in_larger_initial_bound
end MicroCFTA.MergeNumericControlIntegration
