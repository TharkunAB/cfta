import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent

/-!
# Monotone initial parent profile envelopes

Larger initial row, arity, height, and guard limits retain each parent bound.
The row envelope includes both class count and each class path count.
The guard envelope follows the actual own-class step bound.
These comparisons define no completed caller or capacity Plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (classRows passRows parentRows)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le le_trans)
open SourceCurrentAllocatedFiniteOrdinaryGuardOwn (classBudget pathDepth)
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit

private theorem max_mono {a b c d : Nat} (first : a ≤ c) (second : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans first (Nat.le_max_left _ _), Nat.le_trans second (Nat.le_max_right _ _)⟩

/-- Widening every initial class parameter retains its common row envelope. -/
theorem classRows_mono
    {paths largerPaths rows largerRows count largerCount depth largerDepth height largerHeight : Nat}
    (pathBound : paths ≤ largerPaths) (rowBound : rows ≤ largerRows)
    (countBound : count ≤ largerCount) (depthBound : depth ≤ largerDepth) (heightBound : height ≤ largerHeight) :
    classRows paths rows count depth height ≤ classRows largerPaths largerRows largerCount largerDepth largerHeight := by
  have initial := SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_parameters_mono paths
    rowBound countBound depthBound heightBound
  have target := Nat.le_trans initial
    (SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers.targetRows_mono largerRows largerCount largerDepth largerHeight pathBound)
  exact Nat.mul_le_mul (max_mono target rowBound) (max_mono target rowBound)

/-- Every fixed-length tail-first pass is monotone in its initial parameters. -/
theorem passRows_mono (classes : Nat)
    {paths largerPaths rows largerRows count largerCount depth largerDepth height largerHeight : Nat}
    (pathBound : paths ≤ largerPaths) (rowBound : rows ≤ largerRows)
    (countBound : count ≤ largerCount) (depthBound : depth ≤ largerDepth) (heightBound : height ≤ largerHeight) :
    passRows paths count depth height classes rows ≤
      passRows largerPaths largerCount largerDepth largerHeight classes largerRows := by
  induction classes with
  | zero => exact rowBound
  | succ classes ih => exact classRows_mono pathBound ih countBound depthBound heightBound

/-- The initial guard order retains every parent row envelope. -/
theorem parentRows_mono {first last : Limits} (guards : Le first last)
    {rows largerRows count largerCount height largerHeight : Nat}
    (rowBound : rows ≤ largerRows) (countBound : count ≤ largerCount) (heightBound : height ≤ largerHeight) :
    parentRows first rows count height ≤ parentRows last largerRows largerCount largerHeight := by
  have effective := SourceCurrentAllocatedFiniteOrdinaryGuardLimits.effective_mono guards
  have initial := passRows_mono (classBudget first) effective.1 rowBound countBound effective.2 heightBound
  exact Nat.le_trans initial
    (SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.passRows_count_mono
      (classBudget last) largerCount (pathDepth last) largerHeight largerRows effective.1)

/-- Every parent row envelope retains its initial row limit. -/
theorem parentRows_ge (limits : Limits) (rows count height : Nat) : rows ≤ parentRows limits rows count height :=
  SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers.passRows_ge
    (classBudget limits) count (pathDepth limits) height (classBudget limits) rows

/-- Every parent guard envelope retains its initial raw vector. -/
theorem parentGuards_ge (limits : Limits) : Le limits (parentGuards limits) :=
  SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit_ge _ _

/-- Widening the initial raw vector retains the actual parent guard envelope. -/
theorem parentGuards_mono {first last : Limits} (guards : Le first last) :
    Le (parentGuards first) (parentGuards last) :=
  le_trans (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.foldLimit_mono guards _)
    (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.foldLimit_count_mono last
      (Nat.mul_le_mul_left 2 (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.effective_mono guards).1))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone
