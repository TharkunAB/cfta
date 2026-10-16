import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget

/-!
# Native budgets from uniform operand profiles

Uniform row, arity, and height bounds give a constructor reservation.
The reservation does not inspect a future result or execution trace.
Computed literal operand limits fit every supplied uniform profile.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProfileBudget
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
section Generic
variable {Symbol Guard : Type} {rows arity : Nat}

mutual
/-- Computed node limits fit every uniform profile of that node. -/
theorem node_limits_le (value : Value Symbol Guard) (shape : NodeShape rows arity value) :
    (limits value).1 ≤ rows ∧ (limits value).2 ≤ arity := by
  cases value with
  | empty => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | node entry edges depth free =>
      have rest := rows_limits_le edges shape.2
      exact ⟨Nat.max_le.mpr ⟨shape.1, rest.1⟩, rest.2⟩
  | reference | mu | union => cases shape
termination_by sizeOf value

/-- Computed row-list limits fit the common profile of all literal rows. -/
theorem rows_limits_le (edges : List (EdgeValue Symbol Guard)) (shape : RowsShape rows arity edges) :
    (rowsLimits edges).1 ≤ rows ∧ (rowsLimits edges).2 ≤ arity := by
  cases edges with
  | nil => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons edge rest =>
      have first := edge_limits_le edge shape.1
      have later := rows_limits_le rest shape.2
      exact ⟨Nat.max_le.mpr ⟨first.1, later.1⟩, Nat.max_le.mpr ⟨first.2, later.2⟩⟩
termination_by sizeOf edges

/-- Computed edge limits include its arity and fit its common profile. -/
theorem edge_limits_le (edge : EdgeValue Symbol Guard) (shape : EdgeShape rows arity edge) :
    (edgeLimits edge).1 ≤ rows ∧ (edgeLimits edge).2 ≤ arity := by
  cases edge with
  | mk entry children =>
      have rest := children_limits_le children shape.2
      exact ⟨rest.1, Nat.max_le.mpr ⟨shape.1, rest.2⟩⟩
termination_by sizeOf edge

/-- Computed forest limits fit the common profile of all literal children. -/
theorem children_limits_le (values : List (Value Symbol Guard)) (shape : ChildrenShape rows arity values) :
    (childrenLimits values).1 ≤ rows ∧ (childrenLimits values).2 ≤ arity := by
  cases values with
  | nil => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | cons value rest =>
      have first := node_limits_le value shape.1
      have later := children_limits_le rest shape.2
      exact ⟨Nat.max_le.mpr ⟨first.1, later.1⟩, Nat.max_le.mpr ⟨first.2, later.2⟩⟩
termination_by sizeOf values
end

/-- Increasing row and arity limits retains the complete node reservation. -/
theorem node_parameters_mono (firstRows firstArity lastRows lastArity height : Nat)
    (rowBound : firstRows ≤ lastRows) (arityBound : firstArity ≤ lastArity) :
    nodeBudget firstRows firstArity height ≤ nodeBudget lastRows lastArity height := by
  induction height with
  | zero => exact Nat.le_refl _
  | succ height ih =>
      exact Nat.add_le_add_left
        (Nat.mul_le_mul (Nat.mul_le_mul rowBound rowBound)
          (Nat.add_le_add_left (Nat.mul_le_mul arityBound ih) 1)) 1

/-- Increasing the operand limits retains the complete edge reservation. -/
theorem edge_parameters_mono (firstRows firstArity lastRows lastArity height : Nat)
    (rowBound : firstRows ≤ lastRows) (arityBound : firstArity ≤ lastArity) :
    edgeBudget firstRows firstArity height ≤ edgeBudget lastRows lastArity height :=
  Nat.add_le_add_left (Nat.mul_le_mul arityBound
    (node_parameters_mono firstRows firstArity lastRows lastArity height rowBound arityBound)) 1

end Generic
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "height" => MergedOrdinaryHeight.height
local notation "edgeHeight" => MergedOrdinaryHeight.edgeHeight
variable {rows arity : Nat}

/-- A uniform original node profile bounds the literal computed query budget. -/
theorem node_budget_le (left right : Value Symbol Guard)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (bound : Nat) (heights : max (height left) (height right) ≤ bound) :
    SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right ≤ nodeBudget rows arity bound := by
  have limitsBound := children_limits_le [left, right] ⟨leftShape, rightShape, trivial⟩
  exact Nat.le_trans
    (node_parameters_mono _ _ rows arity _ limitsBound.1 limitsBound.2)
    (node_mono rows arity heights)

/-- A uniform original edge profile bounds the literal computed query budget. -/
theorem edge_budget_le (left right : EdgeValue Symbol Guard)
    (leftShape : EdgeShape rows arity left) (rightShape : EdgeShape rows arity right)
    (bound : Nat) (heights : max (edgeHeight left) (edgeHeight right) ≤ bound) :
    SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edgeBudget left right ≤ edgeBudget rows arity bound := by
  have limitsBound := rows_limits_le [left, right] ⟨leftShape, rightShape, trivial⟩
  exact Nat.le_trans
    (edge_parameters_mono _ _ rows arity _ limitsBound.1 limitsBound.2)
    (edge_mono rows arity heights)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProfileBudget
