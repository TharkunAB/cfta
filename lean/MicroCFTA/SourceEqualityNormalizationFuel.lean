import MicroCFTA.SourceCompactGuards

/-!
# Completed normalization fuel agreement

A small completed reference run determines the actual source array result.
The proof does not evaluate the global normalization bound.
-/
namespace MicroCFTA.SourceEqualityNormalizationFuel
open EqualityNormalize

/-- Additional iteration fuel preserves every completed reference result. -/
theorem fixMaybe_add (fuel extra : Nat) (classes : Constraints)
    (finished : fixMaybe fuel classes ≠ .timeout) :
    fixMaybe (fuel + extra) classes = fixMaybe fuel classes := by
  induction fuel generalizing classes with
  | zero => simp [fixMaybe] at finished
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [Nat.succ_add, fixMaybe, stepped]
      | some next =>
          by_cases same : next = classes
          · simp [Nat.succ_add, fixMaybe, stepped, same]
          · have tail : fixMaybe fuel next ≠ .timeout := by
              simpa [fixMaybe, stepped, same] using finished
            simpa [Nat.succ_add, fixMaybe, stepped, same] using ih next tail

/-- Two completed reference executions have the same result. -/
theorem fixMaybe_finished_agree (first second : Nat) (classes : Constraints)
    (firstFinished : fixMaybe first classes ≠ .timeout)
    (secondFinished : fixMaybe second classes ≠ .timeout) :
    fixMaybe first classes = fixMaybe second classes := by
  rcases Nat.le_total first second with earlier | earlier
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le earlier
    exact (fixMaybe_add first extra classes firstFinished).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le earlier
    exact fixMaybe_add second extra classes secondFinished

/-- A completed finite reference run determines the actual source normalizer. -/
theorem normalize_finished (raw : Constraints) (fuel : Nat) (result : RunResult)
    (done : mkEqConstraints fuel raw = result) (finished : result ≠ .timeout) :
    SourceCompactGuards.normalize raw = SymbolicEqualityBridge.resultClasses result := by
  unfold SourceCompactGuards.normalize
  rw [SourceCompactGuards.arrayNormalize_eq]
  have first : fixMaybe fuel (complete (prepare raw)) ≠ .timeout := by
    change mkEqConstraints fuel raw ≠ .timeout
    rw [done]
    exact finished
  have second := EqualityTermination.mkEqConstraints_terminates raw
  have same := fixMaybe_finished_agree fuel (EqualityTermination.normalizationBound raw)
    (complete (prepare raw)) first second
  change SymbolicEqualityBridge.resultClasses (fixMaybe _ _) = _
  rw [← same]
  exact congrArg SymbolicEqualityBridge.resultClasses done

end MicroCFTA.SourceEqualityNormalizationFuel
