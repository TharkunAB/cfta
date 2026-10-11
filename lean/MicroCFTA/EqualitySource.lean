import MicroCFTA.EqualityPartition
import MicroCFTA.EqualityModel

/-!
# Complete source equality normalization

The source's fixed-point loop uses the concrete parent-array completion at
every step. Array-work bounds and iteration bounds are proof instrumentation.
The reference termination theorem supplies a sufficient iteration bound.
-/
namespace MicroCFTA.EqualityIndex
open Language EqualityNormalize EqualityTermination

/-- One actual array completion and strict-prefix contradiction check. -/
def congruenceArray (work : Nat) (classes : Constraints) : RunResult :=
  match completeArray work (addCongruences classes) with
  | none => .timeout
  | some closed => if isContradicting closed then .contradiction else .normalized closed

/-- Turn the source partial-step result into a completed observable result. -/
def stepResult : Option Constraints → RunResult
  | none => .contradiction
  | some classes => .normalized classes

/-- Every actual source step eventually equals the complete reference step. -/
theorem congruenceArray_eventual (classes : Constraints) (active : Active classes) :
    ∃ bound, ∀ work, bound ≤ work → congruenceArray work classes = stepResult (congruenceStep classes) := by
  obtain ⟨bound, complete⟩ := completeArray_eventual (addCongruences classes) (addCongruences_active classes active)
  refine ⟨bound, ?_⟩
  intro work enough
  simp only [congruenceArray, complete work enough, congruenceStep]
  split <;> rfl

/-- The exact source fixed-point schedule, using the parent-array worker. -/
def fixArray (work : Nat) : Nat → Constraints → RunResult
  | 0, _ => .timeout
  | iterations + 1, classes =>
      match congruenceArray work classes with
      | .timeout => .timeout
      | .contradiction => .contradiction
      | .normalized next => if next = classes then .normalized classes else fixArray work iterations next

/-- All array calls in a finite source fixed-point execution have one sufficient bound. -/
theorem fixArray_eventual (iterations : Nat) (classes : Constraints) (active : Active classes) :
    ∃ bound, ∀ work, bound ≤ work → fixArray work iterations classes = fixMaybe iterations classes := by
  induction iterations generalizing classes with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ iterations ih =>
      obtain ⟨firstBound, first⟩ := congruenceArray_eventual classes active
      cases step : congruenceStep classes with
      | none =>
          refine ⟨firstBound, ?_⟩
          intro work enough
          simp [fixArray, first work enough, fixMaybe, step, stepResult]
      | some next =>
          by_cases stable : next = classes
          · refine ⟨firstBound, ?_⟩
            intro work enough
            simp [fixArray, first work enough, fixMaybe, step, stepResult, stable]
          · obtain ⟨restBound, rest⟩ := ih next (congruenceStep_invariants classes next active step).1
            refine ⟨max firstBound restBound, ?_⟩
            intro work enough
            simp [fixArray, first work (by omega), fixMaybe, step, stepResult, stable, rest work (by omega)]

/-- The actual source initialization and repeated array-based normalization. -/
def normalizeArray (iterations work : Nat) (classes : Constraints) : RunResult :=
  match completeArray work (prepare classes) with
  | none => .timeout
  | some initial => fixArray work iterations initial

/-- Initial path-set construction, trivial-class removal, and array completion compose exactly. -/
theorem normalizeArray_eventual (iterations : Nat) (classes : Constraints) :
    ∃ bound, ∀ work, bound ≤ work → normalizeArray iterations work classes = mkEqConstraints iterations classes := by
  obtain ⟨initialBound, initial⟩ := completeArray_eventual (prepare classes) (prepare_active classes)
  obtain ⟨loopBound, loop⟩ := fixArray_eventual iterations (complete (prepare classes))
    (complete_active _ (prepare_active classes))
  refine ⟨max initialBound loopBound, ?_⟩
  intro work enough
  simp only [normalizeArray, initial work (by omega), mkEqConstraints, loop work (by omega)]

/-- The concrete source normalizer terminates and preserves every complete term's equality constraints. -/
theorem source_normalization_exact (classes : Constraints) :
    ∃ workBound, ∀ work, workBound ≤ work →
      normalizeArray (normalizationBound classes) work classes ≠ .timeout ∧
      ∀ term : Term Symbol,
        RunSat term (normalizeArray (normalizationBound classes) work classes) ↔ Satisfies term classes := by
  obtain ⟨bound, agrees⟩ := normalizeArray_eventual (normalizationBound classes) classes
  refine ⟨bound, ?_⟩
  intro work enough
  rw [agrees work enough]
  exact ⟨mkEqConstraints_terminates classes, fun term => mkEqConstraints_total_correct term classes⟩

/-- Source rejection is equivalent to having no finite equality model. -/
theorem source_rejection_exact (symbol : Symbol) (classes : Constraints) :
    ∃ workBound, ∀ work, workBound ≤ work →
      (normalizeArray (normalizationBound classes) work classes = .contradiction ↔
        ¬ ∃ term : Term Symbol, Satisfies term classes) := by
  obtain ⟨bound, agrees⟩ := normalizeArray_eventual (normalizationBound classes) classes
  refine ⟨bound, ?_⟩
  intro work enough
  rw [agrees work enough]
  exact EqualityModel.contradiction_iff_no_model symbol classes

end MicroCFTA.EqualityIndex
