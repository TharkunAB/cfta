import MicroCFTA.SourceCurrentEqualityNormalizationFixed
import MicroCFTA.SourceEqualityConstraintMemoAllocation

/-!
# Normalization fixed points from actual equality operations

Actual normalization and combination derive the stronger ordered fixed-point
invariant of their returned physical payloads. Initial Ready inputs need not
already satisfy this invariant. Contradiction retains its separate case.
-/
namespace MicroCFTA.SourceCurrentEqualityOperationFixed
open SourceEqualityConstraintAllocation SourceEqualityClassOrder
open SourceCurrentEqualityNormalizationFixed (Fixed)
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- Every live physical payload retains its exact class order under source normalization. -/
def FixedPayload (payload : SourceEqualityPrecheck.Constraint) : Prop :=
  ∀ records, payload = some records → Fixed (records.map Record.paths)

private theorem empty_fixed : Fixed [] :=
  SourceCurrentEqualityNormalizationFixed.of_step [] (by intro paths member; cases member)
    (by simp [EqualityNormalize.congruenceStep, EqualityNormalize.complete,
      EqualityNormalize.addCongruences, EqualityNormalize.canonicalize,
      EqualityNormalize.completeFuel, EqualityNormalize.isContradicting])

private theorem combined_fixed (first second : Option EqualityNormalize.Constraints)
    (output : EqualityNormalize.Constraints)
    (actual : SourceCompactGuards.combineEqualities first second = some output) : Fixed output := by
  cases first with
  | none => cases actual
  | some first =>
      cases second with
      | none => cases actual
      | some second =>
          cases first with
          | nil =>
              cases second with
              | nil => cases actual; exact empty_fixed
              | cons head tail => exact SourceCurrentEqualityNormalizationFixed.normalize_idempotent _ _ actual
          | cons head tail =>
              cases second <;> exact SourceCurrentEqualityNormalizationFixed.normalize_idempotent _ _ actual

/-- Actual normalization constructs a Ready fixed physical payload and its complete cache receipt. -/
theorem normalize (classes : EqualityNormalize.Constraints)
    (before : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid before) :
    ∃ result after, SourceEqualityConstraintAllocation.normalize classes before = (.ok result, after) ∧
      Cache.Valid after ∧ Ready after result ∧ Cache.Steps before after ∧ FixedPayload result.payload := by
  obtain ⟨result, after, actual, finalValid, ready, steps, readback⟩ :=
    SourceEqualityConstraintAllocation.normalize_complete classes before valid
  refine ⟨result, after, actual, finalValid, ready, steps, ?_⟩
  intro records live
  have normalized : SourceCompactGuards.normalize classes = some (records.map Record.paths) := by
    simpa only [live, SourceEqualityInheritedPayload.classes, Option.map_some] using readback.symm
  exact SourceCurrentEqualityNormalizationFixed.normalize_idempotent _ _ normalized

/-- Actual cold or warm combination constructs a fixed returned payload from initially Ready operands. -/
theorem combine (first second : Value) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ result,
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok result ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceEqualityConstraintMemoAllocation.combine first second before).2 ∧
      Ready (SourceEqualityConstraintMemoAllocation.combine first second before).2.constraints result ∧
      SourceEqualityConstraintMemoAllocation.Grows before (SourceEqualityConstraintMemoAllocation.combine first second before).2 ∧
      FixedPayload result.payload := by
  obtain ⟨result, actual, finalValid, ready, payload, growth⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct first second before valid firstReady secondReady
  refine ⟨result, actual, finalValid, ready, growth, ?_⟩
  intro records live
  have classes := SourceEqualityConstraintAllocation.read_classes _
    (SourceEqualityGuardReadback.combine_cached _ _) result.payload payload
  have normalized : SourceCompactGuards.combineEqualities
      (SourceEqualityInheritedPayload.classes first.payload)
      (SourceEqualityInheritedPayload.classes second.payload) = some (records.map Record.paths) := by
    simpa only [live, SourceEqualityInheritedPayload.classes, Option.map_some] using classes.symm
  exact combined_fixed _ _ _ normalized

end MicroCFTA.SourceCurrentEqualityOperationFixed
