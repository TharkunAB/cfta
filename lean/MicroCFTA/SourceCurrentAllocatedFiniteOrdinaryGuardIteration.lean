import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardTarget
import MicroCFTA.SourceEqualityClassTarget

/-!
# Ordered guard envelopes for shared class targets

The target uses the literal filtered class paths.
Its query count is bounded by the original class length.
Each edit callback reads an original input position.
The common leaf envelope joins that input with the captured target bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardIteration
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits
open SourceCurrentAllocatedFiniteOrdinaryGuardTarget (foldLimit targetLimit foldLimit_ge)
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits

/-- Increasing the initial vector increases every later fold vector. -/
theorem foldLimit_mono {first last : Limits} (enough : Le first last) (count : Nat) :
    Le (foldLimit first count) (foldLimit last count) := by
  induction count with
  | zero => exact enough
  | succ count ih => exact step_mono ih

/-- More literal queries retain every earlier fold vector. -/
theorem foldLimit_count_mono (limits : Limits) {first last : Nat} (enough : first ≤ last) :
    Le (foldLimit limits first) (foldLimit limits last) := by
  induction last with
  | zero =>
      have same : first = 0 := by omega
      subst first
      exact le_refl _
  | succ last ih =>
      by_cases same : first = last + 1
      · subst first
        exact le_refl _
      · exact le_trans (ih (by omega)) (step_ge _)

/-- Sequential fold query counts add in their literal order. -/
theorem foldLimit_add (limits : Limits) (first last : Nat) :
    foldLimit limits (first + last) = foldLimit (foldLimit limits first) last := by
  induction last with
  | zero => rfl
  | succ last ih => exact congrArg step ih

/-- Filtering the selected path cannot add target operands. -/
theorem operand_paths_length_le (record : SourceEqualityClassOrder.Record) (path : EqualityNormalize.Path) :
    (SourceEqualityClassTarget.operandPaths record.paths path).length ≤ record.paths.length := by
  simp only [SourceEqualityClassTarget.operandPaths, List.length_map, EqualityNarrowing.others]
  exact List.length_filter_le _ _

/-- The literal selected target fits one common original-record envelope. -/
theorem target_le_record (record : SourceEqualityClassOrder.Record) (path : EqualityNormalize.Path) (limits : Limits) :
    Le (targetLimit limits (SourceEqualityClassTarget.operandPaths record.paths path))
      (foldLimit limits record.paths.length) := by
  apply foldLimit_count_mono
  have enough := operand_paths_length_le record path
  exact Nat.le_trans (Nat.sub_le _ _) enough

/-- One leaf joins its captured target envelope with its original input envelope. -/
def leafLimit (record : SourceEqualityClassOrder.Record) (captured input : Limits) : Limits :=
  step (join (foldLimit captured record.paths.length) input)

/-- Increasing either original envelope retains the common leaf bound. -/
theorem leafLimit_mono (record : SourceEqualityClassOrder.Record) {first last input largerInput : Limits}
    (captured : Le first last) (current : Le input largerInput) :
    Le (leafLimit record first input) (leafLimit record last largerInput) :=
  step_mono (join_mono (foldLimit_mono captured _) current)

/-- The common leaf bound retains the original input vector. -/
theorem leafLimit_input_ge (record : SourceEqualityClassOrder.Record) (captured input : Limits) :
    Le input (leafLimit record captured input) :=
  le_trans (le_join_right _ _) (step_ge _)

/-- The common leaf bound retains the original captured vector. -/
theorem captured_le_leafLimit (record : SourceEqualityClassOrder.Record) (captured input : Limits) :
    Le captured (leafLimit record captured input) :=
  le_trans (foldLimit_ge _ _) (le_trans (le_join_left _ _) (step_ge _))

/-- A class with one original vector needs at most its length plus one steps. -/
theorem leafLimit_same (record : SourceEqualityClassOrder.Record) (limits : Limits) :
    Le (leafLimit record limits limits) (foldLimit limits (record.paths.length + 1)) :=
  step_mono (join_le (le_refl _) (foldLimit_ge _ _))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardIteration
