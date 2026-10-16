import MicroCFTA.MergedOrdinaryHeight

/-!
# Whole-expansion constructor Work budgets

Each ordinary node joins at most the square of the row limit.
Each joined edge requests at most the arity limit of child intersections.
The bounds count every repeated subproblem. They do not count instructions.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers

/-- Count constructor Work for the complete ordinary expansion at a height. -/
def nodeBudget (rows arity : Nat) : Nat → Nat
  | 0 => 1
  | height + 1 => 1 + rows * rows * (1 + arity * nodeBudget rows arity height)

/-- Count constructor Work for paired children and the final edge constructor. -/
def edgeBudget (rows arity height : Nat) : Nat := 1 + arity * nodeBudget rows arity height

/-- Every node budget permits one constructor Work request. -/
theorem node_positive (rows arity height : Nat) : 1 ≤ nodeBudget rows arity height := by
  cases height <;> simp only [nodeBudget] <;> omega

/-- Every edge budget permits one constructor Work request. -/
theorem edge_positive (rows arity height : Nat) : 1 ≤ edgeBudget rows arity height := by
  simp only [edgeBudget]
  omega

/-- Adding one ordinary layer cannot reduce the node budget. -/
theorem node_succ (rows arity height : Nat) : nodeBudget rows arity height ≤ nodeBudget rows arity (height + 1) := by
  induction height with
  | zero => exact node_positive rows arity 1
  | succ height ih =>
      simp only [nodeBudget]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) 1)) 1

/-- Larger input height permits the same complete node expansion. -/
theorem node_mono (rows arity : Nat) {first last : Nat} (bounded : first ≤ last) :
    nodeBudget rows arity first ≤ nodeBudget rows arity last := by
  induction bounded with
  | refl => exact Nat.le_refl _
  | @step last bounded ih => exact Nat.le_trans ih (node_succ rows arity last)

/-- Larger child height permits the same complete edge expansion. -/
theorem edge_mono (rows arity : Nat) {first last : Nat} (bounded : first ≤ last) :
    edgeBudget rows arity first ≤ edgeBudget rows arity last := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left arity (node_mono rows arity bounded)) 1

/-- The next node layer permits the whole row-pair expansion and its constructor. -/
theorem node_step (rows arity height : Nat) :
    nodeBudget rows arity (height + 1) = 1 + rows * rows * edgeBudget rows arity height := rfl

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
