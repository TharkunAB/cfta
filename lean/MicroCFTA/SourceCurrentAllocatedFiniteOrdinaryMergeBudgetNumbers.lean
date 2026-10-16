import MicroCFTA.MergedOrdinaryHeight

/-!
# Complete ordinary Merge constructor request budgets

Each lower column layer permits the square of the original row limit.
The bounds include repeated recursive requests and the final constructors.
Zero ordinary height needs no constructor request.
These numbers do not bound instructions or host evaluations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers

/-- Bound node constructor requests through every ordinary column layer. -/
def nodeBudget (rows arity : Nat) : Nat → Nat
  | 0 => 0
  | height + 1 => 1 + rows * arity * (1 + nodeBudget (rows * rows) arity height)

/-- Bound edge constructor requests through every ordinary column layer. -/
def edgeBudget (rows arity : Nat) : Nat → Nat
  | 0 => 0
  | height + 1 => rows + rows * arity * edgeBudget (rows * rows) arity height

/-- Increasing row and arity limits retains every permitted node request. -/
theorem node_parameters_mono (height : Nat) {firstRows lastRows firstArity lastArity : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) :
    nodeBudget firstRows firstArity height ≤ nodeBudget lastRows lastArity height := by
  induction height generalizing firstRows lastRows firstArity lastArity with
  | zero => exact Nat.le_refl _
  | succ height ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rows arity)
        (Nat.add_le_add_left (ih (Nat.mul_le_mul rows rows) arity) 1)) 1

/-- Increasing row and arity limits retains every permitted edge request. -/
theorem edge_parameters_mono (height : Nat) {firstRows lastRows firstArity lastArity : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) :
    edgeBudget firstRows firstArity height ≤ edgeBudget lastRows lastArity height := by
  induction height generalizing firstRows lastRows firstArity lastArity with
  | zero => exact Nat.le_refl _
  | succ height ih =>
      exact Nat.add_le_add rows (Nat.mul_le_mul (Nat.mul_le_mul rows arity)
        (ih (Nat.mul_le_mul rows rows) arity))

/-- Increasing only the original row limit retains the node budget. -/
theorem node_rows_mono (arity height : Nat) {first last : Nat} (enough : first ≤ last) :
    nodeBudget first arity height ≤ nodeBudget last arity height :=
  node_parameters_mono height enough (Nat.le_refl _)

/-- Increasing only the original row limit retains the edge budget. -/
theorem edge_rows_mono (arity height : Nat) {first last : Nat} (enough : first ≤ last) :
    edgeBudget first arity height ≤ edgeBudget last arity height :=
  edge_parameters_mono height enough (Nat.le_refl _)

/-- Increasing only the arity limit retains the node budget. -/
theorem node_arity_mono (rows height : Nat) {first last : Nat} (enough : first ≤ last) :
    nodeBudget rows first height ≤ nodeBudget rows last height :=
  node_parameters_mono height (Nat.le_refl _) enough

/-- Increasing only the arity limit retains the edge budget. -/
theorem edge_arity_mono (rows height : Nat) {first last : Nat} (enough : first ≤ last) :
    edgeBudget rows first height ≤ edgeBudget rows last height :=
  edge_parameters_mono height (Nat.le_refl _) enough

/-- One more ordinary layer retains the node budget. -/
theorem node_succ (rows arity height : Nat) :
    nodeBudget rows arity height ≤ nodeBudget rows arity (height + 1) := by
  induction height generalizing rows arity with
  | zero => exact Nat.zero_le _
  | succ height ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (rows * arity)
        (Nat.add_le_add_left (ih (rows * rows) arity) 1)) 1

/-- One more ordinary layer retains the edge budget. -/
theorem edge_succ (rows arity height : Nat) :
    edgeBudget rows arity height ≤ edgeBudget rows arity (height + 1) := by
  induction height generalizing rows arity with
  | zero => exact Nat.zero_le _
  | succ height ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul_left (rows * arity) (ih (rows * rows) arity)) rows

/-- A larger ordinary height retains the node budget. -/
theorem node_mono (rows arity : Nat) {first last : Nat} (enough : first ≤ last) :
    nodeBudget rows arity first ≤ nodeBudget rows arity last := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (node_succ rows arity last)

/-- A larger ordinary height retains the edge budget. -/
theorem edge_mono (rows arity : Nat) {first last : Nat} (enough : first ≤ last) :
    edgeBudget rows arity first ≤ edgeBudget rows arity last := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (edge_succ rows arity last)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers
