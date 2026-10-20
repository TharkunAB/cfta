import MicroCFTA.SourceCompactGuards

/-!
# Completed normalization receipts determine the actual source result

Two completed reference schedules have the same result. A small completed
receipt therefore identifies the actual source array result without
evaluating its conservative sufficient bound. The fallback retains the
actual source call when the small reference schedule does not complete.
-/
namespace MicroCFTA.SourceEqualityNormalizationReceipt
open EqualityNormalize

/-- Completed fixed-point schedules agree at every pair of bounds. -/
theorem fixMaybe_unique (first second : Nat) (classes : Constraints)
    (firstFinished : fixMaybe first classes ≠ .timeout) (secondFinished : fixMaybe second classes ≠ .timeout) :
    fixMaybe first classes = fixMaybe second classes := by
  induction first generalizing second classes with
  | zero => exact False.elim (firstFinished rfl)
  | succ first ih =>
      cases second with
      | zero => exact False.elim (secondFinished rfl)
      | succ second =>
          cases next : congruenceStep classes with
          | none => simp only [fixMaybe, next]
          | some output =>
              by_cases stable : output = classes
              · simp only [fixMaybe, next, stable, ↓reduceIte]
              · have left : fixMaybe first output ≠ .timeout := by simpa only [fixMaybe, next, stable, ↓reduceIte] using firstFinished
                have right : fixMaybe second output ≠ .timeout := by simpa only [fixMaybe, next, stable, ↓reduceIte] using secondFinished
                simpa only [fixMaybe, next, stable, ↓reduceIte] using ih second output left right

/-- A completed reference receipt is identical to the actual total source array result. -/
theorem array_eq (fuel : Nat) (classes : Constraints) (finished : mkEqConstraints fuel classes ≠ .timeout) :
    SourceCompactGuards.arrayNormalize classes = mkEqConstraints fuel classes := by
  rw [SourceCompactGuards.arrayNormalize_eq]
  exact fixMaybe_unique _ _ _ (EqualityTermination.mkEqConstraints_terminates classes) finished

/-- Use a completed small receipt and retain the actual source call on an incomplete schedule. -/
noncomputable def observed (fuel : Nat) (classes : Constraints) : RunResult :=
  match mkEqConstraints fuel classes with
  | .timeout => SourceCompactGuards.arrayNormalize classes
  | .contradiction => .contradiction
  | .normalized output => .normalized output

/-- The small-receipt observation is an exact equation for the actual source array operation. -/
theorem observed_eq (fuel : Nat) (classes : Constraints) : SourceCompactGuards.arrayNormalize classes = observed fuel classes := by
  cases done : mkEqConstraints fuel classes with
  | timeout => simp only [observed, done]
  | contradiction => simpa only [observed, done] using array_eq fuel classes (by simp [done])
  | normalized output => simpa only [observed, done] using array_eq fuel classes (by simp [done])

end MicroCFTA.SourceEqualityNormalizationReceipt
