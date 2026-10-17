import MicroCFTA.SourceCurrentEqualityNormalizationFixed
import MicroCFTA.SourceCurrentEqualityDescendFixed
import MicroCFTA.SourceEqualityConstraintMemoAllocation
import MicroCFTA.SourceCurrentAllocatedInheritedPrefix

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

/-- Actual indexed descent preserves fixedness together with readiness and complete operation growth. -/
theorem descend (input : Value) (index : Nat) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints input) (fixed : FixedPayload input.payload) :
    let actual := SourceEqualityConstraintMemoAllocation.descend input index before
    SourceEqualityConstraintMemoAllocation.Valid actual.2 ∧ Ready actual.2.constraints actual.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows before actual.2 ∧ FixedPayload actual.1.payload := by
  have checked := SourceEqualityConstraintMemoAllocation.descend_correct input index before valid ready
  refine ⟨checked.1, checked.2.1, checked.2.2.2, ?_⟩
  intro records live
  apply SourceCurrentEqualityDescendFixed.descend_fixed input.payload ready.2 fixed index records
  rw [← checked.2.2.1]
  exact live

/-- Initial Ready operands derive a fixed child payload through actual combination and indexed descent. -/
theorem combine_then_descend (first second : Value) (index : Nat) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ combined,
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok combined ∧
      let middle := (SourceEqualityConstraintMemoAllocation.combine first second before).2
      let actual := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      SourceEqualityConstraintMemoAllocation.Valid actual.2 ∧ Ready actual.2.constraints actual.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle actual.2 ∧ FixedPayload actual.1.payload := by
  obtain ⟨combined, actual, middleValid, combinedReady, growth, fixed⟩ :=
    combine first second before valid firstReady secondReady
  exact ⟨combined, actual, middleValid, combinedReady, growth,
    descend combined index _ middleValid combinedReady fixed⟩

/-- The actual accessor and inherited prefix derive fixedness from initial field availability. -/
theorem inherited_prefix (original : SourceSymbolicIndex.Constraint FullSyntax.Formula)
    (input : Value) (before : Operations) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints input)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original) :
    ∃ result,
      (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some result) ∧
      SourceEqualityConstraintMemoAllocation.Valid (SourceCurrentAllocatedInheritedPrefix.run original input before).2 ∧
      Ready (SourceCurrentAllocatedInheritedPrefix.run original input before).2.constraints result ∧
      SourceEqualityConstraintMemoAllocation.Grows before (SourceCurrentAllocatedInheritedPrefix.run original input before).2 ∧
      FixedPayload result.payload := by
  cases input with
  | contradiction =>
      exact ⟨.contradiction, rfl, valid, ready, SourceEqualityConstraintMemoAllocation.grows_refl before,
        by intro records impossible; cases impossible⟩
  | live identity records =>
      obtain ⟨own, loaded, accessorValid, ownReady, _, _, accessorGrowth⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      obtain ⟨result, actual, finalValid, resultReady, growth, fixed⟩ :=
        combine (.live identity records) own _ accessorValid (ready.grows accessorGrowth.constraint_growth) ownReady
      rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before own loaded]
      exact ⟨result, by simp only [actual, Except.map], finalValid, resultReady,
        SourceCurrentConjunctionEquality.grows_trans accessorGrowth growth, fixed⟩

/-- Initial inherited and field data construct fixed child payloads through the actual full prefix. -/
theorem prefix_descend (original : SourceSymbolicIndex.Constraint FullSyntax.Formula)
    (input : Value) (index : Nat) (before : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : Ready before.constraints input)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original) :
    ∃ combined,
      (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some combined) ∧
      let middle := (SourceCurrentAllocatedInheritedPrefix.run original input before).2
      let actual := SourceEqualityConstraintMemoAllocation.descend combined index middle
      SourceEqualityConstraintMemoAllocation.Valid middle ∧ Ready middle.constraints combined ∧
      SourceEqualityConstraintMemoAllocation.Grows before middle ∧
      SourceEqualityConstraintMemoAllocation.Valid actual.2 ∧ Ready actual.2.constraints actual.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows middle actual.2 ∧ FixedPayload actual.1.payload := by
  obtain ⟨combined, actual, middleValid, combinedReady, growth, fixed⟩ := inherited_prefix original input before valid ready field
  exact ⟨combined, actual, middleValid, combinedReady, growth,
    descend combined index _ middleValid combinedReady fixed⟩

end MicroCFTA.SourceCurrentEqualityOperationFixed
