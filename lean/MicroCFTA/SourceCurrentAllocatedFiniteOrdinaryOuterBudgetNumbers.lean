import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers

/-!
# Initial constructor request budgets for ordinary outer traversal

Each row pays for Parent and traversal of its returned children.
The node then pays for its raw reconstruction. Warm calls can use less.
The functions charge every literal occurrence. They assume no distinct keys.
These pure bounds do not construct an execution or a capacity Plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le le_refl le_trans)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformMonotone
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
local notation "ParentN" => SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget
local notation "ParentE" => SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit

/-- Each ordinary node pays for its rows and at most one raw node request. -/
def nodeNodes (rows arity : Nat) (guards : Limits) : Nat → Nat
  | 0 => 0
  | height + 1 => 1 + rows * (ParentN guards rows arity height + max arity 1 *
      nodeNodes (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height)

/-- Each row pays for Parent, its returned child calls, and one raw edge request. -/
def nodeEdges (rows arity : Nat) (guards : Limits) : Nat → Nat
  | 0 => 0
  | height + 1 => rows * (ParentE guards rows arity height + 1 + max arity 1 *
      nodeEdges (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height)

/-- One original row pays for its parent and all returned child node requests. -/
def rowNodes (rows arity : Nat) (guards : Limits) (height : Nat) : Nat :=
  ParentN guards rows arity height + max arity 1 *
    nodeNodes (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height

/-- The returned parent's raw edge rebuild occurs after its child calls. -/
def rowEdges (rows arity : Nat) (guards : Limits) (height : Nat) : Nat :=
  ParentE guards rows arity height + 1 + max arity 1 *
    nodeEdges (parentRows guards rows arity height) (max arity 1) (parentGuards guards) height

/-- Descendants uses its supplied returned edge profile without a second parent call. -/
def descendantsNodes (rows arity : Nat) (guards : Limits) (height : Nat) : Nat :=
  arity * nodeNodes rows arity guards height

/-- Descendants permits one raw edge request after the returned child traversal. -/
def descendantsEdges (rows arity : Nat) (guards : Limits) (height : Nat) : Nat :=
  1 + arity * nodeEdges rows arity guards height

/-- The next node level includes every original row and its raw node reconstruction. -/
theorem node_step (rows arity : Nat) (guards : Limits) (height : Nat) :
    nodeNodes rows arity guards (height + 1) = 1 + rows * rowNodes rows arity guards height ∧
      nodeEdges rows arity guards (height + 1) = rows * rowEdges rows arity guards height := ⟨rfl, rfl⟩

private theorem max_mono {a b c d : Nat} (first : a ≤ c) (second : b ≤ d) : max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans first (Nat.le_max_left _ _), Nat.le_trans second (Nat.le_max_right _ _)⟩

/-- Larger input rows, arity, and guards retain both complete traversal budgets. -/
theorem parameters_mono (height : Nat) {rows largerRows arity largerArity : Nat} {guards largerGuards : Limits}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (guardBound : Le guards largerGuards) :
    nodeNodes rows arity guards height ≤ nodeNodes largerRows largerArity largerGuards height ∧
      nodeEdges rows arity guards height ≤ nodeEdges largerRows largerArity largerGuards height := by
  induction height generalizing rows largerRows arity largerArity guards largerGuards with
  | zero => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ height ih =>
      rw [nodeNodes, nodeNodes, nodeEdges, nodeEdges]
      have parents := SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.parameters_mono
        guardBound rowBound arityBound (Nat.le_refl height)
      have child := ih (parentRows_mono guardBound rowBound arityBound (Nat.le_refl height))
        (max_mono arityBound (Nat.le_refl 1)) (parentGuards_mono guardBound)
      exact ⟨Nat.add_le_add_left (Nat.mul_le_mul rowBound
          (Nat.add_le_add parents.1 (Nat.mul_le_mul (max_mono arityBound (Nat.le_refl 1)) child.1))) 1,
        Nat.mul_le_mul rowBound (Nat.add_le_add (Nat.add_le_add_right parents.2 1)
          (Nat.mul_le_mul (max_mono arityBound (Nat.le_refl 1)) child.2))⟩

/-- One additional height level retains both earlier traversal budgets. -/
theorem height_step (rows arity : Nat) (guards : Limits) (height : Nat) :
    nodeNodes rows arity guards height ≤ nodeNodes rows arity guards (height + 1) ∧
      nodeEdges rows arity guards height ≤ nodeEdges rows arity guards (height + 1) := by
  induction height generalizing rows arity guards with
  | zero => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | succ height ih =>
      rw [nodeNodes, nodeNodes, nodeEdges, nodeEdges]
      have old := ih (parentRows guards rows arity height) (max arity 1) (parentGuards guards)
      have widened := parameters_mono (height + 1)
        (parentRows_mono (le_refl guards) (Nat.le_refl rows) (Nat.le_refl arity) (Nat.le_succ height))
        (Nat.le_refl (max arity 1)) (le_refl (parentGuards guards))
      have parents := SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.parameters_mono
        (le_refl guards) (Nat.le_refl rows) (Nat.le_refl arity) (Nat.le_succ height)
      have childNodes := Nat.le_trans old.1 widened.1
      have childEdges := Nat.le_trans old.2 widened.2
      exact ⟨Nat.add_le_add_left (Nat.mul_le_mul_left rows
          (Nat.add_le_add parents.1 (Nat.mul_le_mul_left (max arity 1) childNodes))) 1,
        Nat.mul_le_mul_left rows (Nat.add_le_add (Nat.add_le_add_right parents.2 1)
          (Nat.mul_le_mul_left (max arity 1) childEdges))⟩

/-- A larger initial height permits both earlier complete traversal budgets. -/
theorem height_mono (rows arity : Nat) (guards : Limits) {first last : Nat} (bound : first ≤ last) :
    nodeNodes rows arity guards first ≤ nodeNodes rows arity guards last ∧
      nodeEdges rows arity guards first ≤ nodeEdges rows arity guards last := by
  induction bound with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | @step last _ ih =>
      have next := height_step rows arity guards last
      exact ⟨Nat.le_trans ih.1 next.1, Nat.le_trans ih.2 next.2⟩

/-- Widening every original parameter retains both complete traversal budgets. -/
theorem mono {rows largerRows arity largerArity firstHeight lastHeight : Nat} {guards largerGuards : Limits}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (guardBound : Le guards largerGuards)
    (heightBound : firstHeight ≤ lastHeight) :
    nodeNodes rows arity guards firstHeight ≤ nodeNodes largerRows largerArity largerGuards lastHeight ∧
      nodeEdges rows arity guards firstHeight ≤ nodeEdges largerRows largerArity largerGuards lastHeight := by
  have first := parameters_mono firstHeight rowBound arityBound guardBound
  have last := height_mono largerRows largerArity largerGuards heightBound
  exact ⟨Nat.le_trans first.1 last.1, Nat.le_trans first.2 last.2⟩

/-- One original row retains its whole budget under wider initial parameters. -/
theorem row_mono {rows largerRows arity largerArity firstHeight lastHeight : Nat} {guards largerGuards : Limits}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (guardBound : Le guards largerGuards)
    (heightBound : firstHeight ≤ lastHeight) :
    rowNodes rows arity guards firstHeight ≤ rowNodes largerRows largerArity largerGuards lastHeight ∧
      rowEdges rows arity guards firstHeight ≤ rowEdges largerRows largerArity largerGuards lastHeight := by
  have parents := SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.parameters_mono
    guardBound rowBound arityBound heightBound
  have child := mono (parentRows_mono guardBound rowBound arityBound heightBound)
    (max_mono arityBound (Nat.le_refl 1)) (parentGuards_mono guardBound) heightBound
  exact ⟨Nat.add_le_add parents.1 (Nat.mul_le_mul (max_mono arityBound (Nat.le_refl 1)) child.1),
    Nat.add_le_add (Nat.add_le_add_right parents.2 1) (Nat.mul_le_mul (max_mono arityBound (Nat.le_refl 1)) child.2)⟩

/-- A returned edge's descendant budget widens without another parent charge. -/
theorem descendants_mono {rows largerRows arity largerArity firstHeight lastHeight : Nat} {guards largerGuards : Limits}
    (rowBound : rows ≤ largerRows) (arityBound : arity ≤ largerArity) (guardBound : Le guards largerGuards)
    (heightBound : firstHeight ≤ lastHeight) :
    descendantsNodes rows arity guards firstHeight ≤ descendantsNodes largerRows largerArity largerGuards lastHeight ∧
      descendantsEdges rows arity guards firstHeight ≤ descendantsEdges largerRows largerArity largerGuards lastHeight := by
  have child := mono rowBound arityBound guardBound heightBound
  exact ⟨Nat.mul_le_mul arityBound child.1, Nat.add_le_add_left (Nat.mul_le_mul arityBound child.2) 1⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
