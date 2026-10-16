import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone

/-!
# Height-indexed outer output profile envelopes

Each original row first runs its parent reduction.
The returned children then use the smaller ordinary height bound.
Row and raw guard envelopes can grow while that height decreases.
These pure transforms do not assert an execution or a returned-cell law.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le le_refl le_trans)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit

/-- A node retains its original row count and every returned descendant row bound. -/
def nodeRows (rows arity : Nat) (guards : Limits) : Nat → Nat
  | 0 => rows
  | height + 1 => max rows (nodeRows (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height)

/-- A node retains the guard envelope produced after parent reduction and child descent. -/
def nodeGuards (rows arity : Nat) (guards : Limits) : Nat → Limits
  | 0 => guards
  | height + 1 => nodeGuards (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height

/-- Every node output envelope retains its initial row bound. -/
theorem nodeRows_ge (rows arity : Nat) (guards : Limits) (height : Nat) : rows ≤ nodeRows rows arity guards height := by
  cases height with
  | zero => exact Nat.le_refl _
  | succ height => exact Nat.le_max_left _ _

/-- Every node output guard envelope retains its initial raw vector. -/
theorem nodeGuards_ge (rows arity : Nat) (guards : Limits) (height : Nat) : Le guards (nodeGuards rows arity guards height) := by
  induction height generalizing rows arity guards with
  | zero => exact le_refl _
  | succ height ih => exact le_trans (parentGuards_ge guards) (ih _ _ _)

private theorem max_mono {a b c d : Nat} (first : a ≤ c) (second : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans first (Nat.le_max_left _ _), Nat.le_trans second (Nat.le_max_right _ _)⟩

/-- Widening initial rows, arity, and guards retains both outer output envelopes. -/
theorem parameters_mono (height : Nat) {rows largerRows arity largerArity : Nat} {guards largerGuards : Limits}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (guardBound : Le guards largerGuards) :
    nodeRows rows arity guards height ≤ nodeRows largerRows largerArity largerGuards height ∧
      Le (nodeGuards rows arity guards height) (nodeGuards largerRows largerArity largerGuards height) := by
  induction height generalizing rows largerRows arity largerArity guards largerGuards with
  | zero => exact ⟨rowBound, guardBound⟩
  | succ height ih =>
      have smaller := ih (parentRows_mono guardBound rowBound arityBound (Nat.le_refl height))
        (max_mono arityBound (Nat.le_refl 1)) (parentGuards_mono guardBound)
      exact ⟨max_mono rowBound smaller.1, smaller.2⟩

/-- One additional ordinary height level retains both earlier output envelopes. -/
theorem height_step (rows arity : Nat) (guards : Limits) (height : Nat) :
    nodeRows rows arity guards height ≤ nodeRows rows arity guards (height + 1) ∧
      Le (nodeGuards rows arity guards height) (nodeGuards rows arity guards (height + 1)) := by
  induction height generalizing rows arity guards with
  | zero => exact ⟨nodeRows_ge _ _ _ _, nodeGuards_ge _ _ _ _⟩
  | succ height ih =>
      have previous := ih (parentRows guards rows arity height) (max arity 1) (parentGuards guards)
      have widened := parameters_mono (height + 1)
        (parentRows_mono (le_refl guards) (Nat.le_refl rows) (Nat.le_refl arity) (Nat.le_succ height))
        (Nat.le_refl (max arity 1)) (le_refl (parentGuards guards))
      exact ⟨max_mono (Nat.le_refl rows) (Nat.le_trans previous.1 widened.1), le_trans previous.2 widened.2⟩

/-- A larger initial height bound retains both earlier outer envelopes. -/
theorem height_mono (rows arity : Nat) (guards : Limits) {first last : Nat} (enough : first ≤ last) :
    nodeRows rows arity guards first ≤ nodeRows rows arity guards last ∧
      Le (nodeGuards rows arity guards first) (nodeGuards rows arity guards last) := by
  induction enough with
  | refl => exact ⟨Nat.le_refl _, le_refl _⟩
  | @step last _ ih =>
      have next := height_step rows arity guards last
      exact ⟨Nat.le_trans ih.1 next.1, le_trans ih.2 next.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers
