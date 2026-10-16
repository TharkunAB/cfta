import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers

/-!
# Initial profile and constructor budgets for the rotated Target fold

The base computes the seed operand. Each later step computes one operand,
then the shorter tail, then the native query at that tail's return.
The height limit stays fixed. Both constructor supplies conservatively use
the native budget for all Work. These numbers assume no execution receipt.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
namespace Operand
export SourceCurrentAllocatedFiniteOrdinaryOperandResources (nodeBudget edgeBudget)
end Operand
namespace Native
export SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers (nodeBudget)
end Native
namespace Merge
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
end Merge
namespace Occurrences
export SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds (nodeCount)
end Occurrences
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open SourceCurrentAllocatedFiniteOrdinaryProjectionProfile (forestRows projectRows)

/-- Every initial operand has the same projection and Merge row envelope. -/
def operandRows (rows count depth bound : Nat) : Nat := envelope (forestRows rows count depth) bound

/-- Each additional native intersection squares the common input row limit. -/
def foldRows (base : Nat) : Nat → Nat
  | 0 => base
  | steps + 1 => max base (foldRows base steps) * max base (foldRows base steps)

/-- Charge the current operand, the shorter tail, then the exact next query limit. -/
def foldNodes (operand base arity bound : Nat) : Nat → Nat
  | 0 => operand
  | steps + 1 => operand + foldNodes operand base arity bound steps +
      Native.nodeBudget (max base (foldRows base steps)) arity bound

/-- Edge supply uses the same conservative native Work bound with its own operand cost. -/
def foldEdges (operand base arity bound : Nat) (steps : Nat) : Nat := foldNodes operand base arity bound steps

/-- Bound every returned Target profile from the original captured forest. -/
def targetRows (rows count depth bound steps : Nat) : Nat := foldRows (operandRows rows count depth bound) steps

/-- Bound all Target node requests using only original forest limits. -/
def nodeBudget (rows arity count depth bound steps : Nat) : Nat :=
  foldNodes (Operand.nodeBudget rows arity count depth bound) (operandRows rows count depth bound) (max arity 1) bound steps

/-- Bound all Target edge requests using only original forest limits. -/
def edgeBudget (rows arity count depth bound steps : Nat) : Nat :=
  foldEdges (Operand.edgeBudget rows arity count depth bound) (operandRows rows count depth bound) (max arity 1) bound steps

private theorem max_mono {first last otherFirst otherLast : Nat} (one : first ≤ last) (other : otherFirst ≤ otherLast) :
    max first otherFirst ≤ max last otherLast :=
  Nat.max_le.mpr ⟨Nat.le_trans one (Nat.le_max_left _ _), Nat.le_trans other (Nat.le_max_right _ _)⟩

/-- Every shorter result retains the common operand row envelope. -/
theorem base_le_foldRows (base steps : Nat) : base ≤ foldRows base steps := by
  cases steps with
  | zero => exact Nat.le_refl _
  | succ steps => exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_mul_self _)

/-- One more native query cannot decrease the row envelope. -/
theorem foldRows_succ (base steps : Nat) : foldRows base steps ≤ foldRows base (steps + 1) :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_mul_self _)

/-- The common operand already fits every tail, so the maximum is the tail limit. -/
theorem foldRows_succ_square (base steps : Nat) :
    foldRows base (steps + 1) = foldRows base steps * foldRows base steps := by
  simp only [foldRows, Nat.max_eq_right (base_le_foldRows base steps)]

/-- More additional operands cannot decrease the row envelope. -/
theorem foldRows_mono (base : Nat) {first last : Nat} (enough : first ≤ last) : foldRows base first ≤ foldRows base last := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (foldRows_succ base last)

/-- A larger common operand profile permits every earlier tail profile. -/
theorem foldRows_parameters_mono (steps : Nat) {first last : Nat} (enough : first ≤ last) :
    foldRows first steps ≤ foldRows last steps := by
  induction steps with
  | zero => exact enough
  | succ steps ih => exact Nat.mul_le_mul (max_mono enough ih) (max_mono enough ih)

/-- One more operand and query cannot reduce the node request budget. -/
theorem foldNodes_succ (operand base arity bound steps : Nat) :
    foldNodes operand base arity bound steps ≤ foldNodes operand base arity bound (steps + 1) := by
  simp only [foldNodes]
  omega

/-- More additional operands cannot reduce the node request budget. -/
theorem foldNodes_mono (operand base arity bound : Nat) {first last : Nat} (enough : first ≤ last) :
    foldNodes operand base arity bound first ≤ foldNodes operand base arity bound last := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (foldNodes_succ operand base arity bound last)

/-- More additional operands cannot reduce the edge request budget. -/
theorem foldEdges_mono (operand base arity bound : Nat) {first last : Nat} (enough : first ≤ last) :
    foldEdges operand base arity bound first ≤ foldEdges operand base arity bound last :=
  foldNodes_mono operand base arity bound enough

private theorem native_parameters_mono (bound : Nat) {firstRows lastRows firstArity lastArity : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) :
    Native.nodeBudget firstRows firstArity bound ≤ Native.nodeBudget lastRows lastArity bound := by
  induction bound with
  | zero => exact Nat.le_refl _
  | succ bound ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rows rows)
        (Nat.add_le_add_left (Nat.mul_le_mul arity ih) 1)) 1

/-- Increasing initial costs, rows, arity, or height retains the complete node budget. -/
theorem foldNodes_parameters_mono (steps : Nat)
    {firstOperand lastOperand firstRows lastRows firstArity lastArity firstBound lastBound : Nat}
    (operand : firstOperand ≤ lastOperand) (rows : firstRows ≤ lastRows)
    (arity : firstArity ≤ lastArity) (bound : firstBound ≤ lastBound) :
    foldNodes firstOperand firstRows firstArity firstBound steps ≤ foldNodes lastOperand lastRows lastArity lastBound steps := by
  induction steps with
  | zero => exact operand
  | succ steps ih =>
      have inputs := max_mono rows (foldRows_parameters_mono steps rows)
      have query := Nat.le_trans (native_parameters_mono firstBound inputs arity)
        (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.node_mono _ _ bound)
      exact Nat.add_le_add (Nat.add_le_add operand ih) query

/-- Increasing initial costs, rows, arity, or height retains the complete edge budget. -/
theorem foldEdges_parameters_mono (steps : Nat)
    {firstOperand lastOperand firstRows lastRows firstArity lastArity firstBound lastBound : Nat}
    (operand : firstOperand ≤ lastOperand) (rows : firstRows ≤ lastRows)
    (arity : firstArity ≤ lastArity) (bound : firstBound ≤ lastBound) :
    foldEdges firstOperand firstRows firstArity firstBound steps ≤ foldEdges lastOperand lastRows lastArity lastBound steps :=
  foldNodes_parameters_mono steps operand rows arity bound

private theorem forest_parameters_mono {firstRows lastRows firstCount lastCount firstDepth lastDepth : Nat}
    (rows : firstRows ≤ lastRows) (count : firstCount ≤ lastCount) (depth : firstDepth ≤ lastDepth) :
    forestRows firstRows firstCount firstDepth ≤ forestRows lastRows lastCount lastDepth := by
  have profile := Nat.pow_le_pow_left (max_mono (Nat.le_refl 1) rows) (firstDepth + 1)
  exact Nat.le_trans (Nat.mul_le_mul (max_mono (Nat.le_refl 1) count) profile)
    (Nat.mul_le_mul_left _ (SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.projectRows_mono lastRows depth))

/-- Larger original forest and height limits retain each operand row envelope. -/
theorem operandRows_mono {firstRows lastRows firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    operandRows firstRows firstCount firstDepth firstBound ≤ operandRows lastRows lastCount lastDepth lastBound :=
  Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope_rows_mono firstBound
    (forest_parameters_mono rows count depth))
    (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope_height_mono _ bound)

/-- Every tail result permits the original operand row envelope. -/
theorem operandRows_le_foldRows (rows count depth bound steps : Nat) :
    operandRows rows count depth bound ≤ targetRows rows count depth bound steps :=
  base_le_foldRows _ steps

/-- The seed-only Target retains its single operand row envelope. -/
theorem targetRows_base (rows count depth bound : Nat) : targetRows rows count depth bound 0 = operandRows rows count depth bound := rfl

/-- Each added operand joins the common operand limit with the shorter tail limit. -/
theorem targetRows_step (rows count depth bound steps : Nat) :
    targetRows rows count depth bound (steps + 1) =
      max (operandRows rows count depth bound) (targetRows rows count depth bound steps) *
        max (operandRows rows count depth bound) (targetRows rows count depth bound steps) := rfl

/-- More additional operands cannot reduce the initial-only output profile. -/
theorem targetRows_mono (rows count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    targetRows rows count depth bound first ≤ targetRows rows count depth bound last := foldRows_mono _ enough

/-- Larger original forest limits retain every Target output profile. -/
theorem targetRows_parameters_mono (steps : Nat)
    {firstRows lastRows firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    targetRows firstRows firstCount firstDepth firstBound steps ≤ targetRows lastRows lastCount lastDepth lastBound steps :=
  foldRows_parameters_mono steps (operandRows_mono rows count depth bound)

/-- The seed-only Target charges one actual operand node budget. -/
theorem nodeBudget_base (rows arity count depth bound : Nat) :
    nodeBudget rows arity count depth bound 0 = Operand.nodeBudget rows arity count depth bound := rfl

/-- The seed-only Target charges one actual operand edge budget. -/
theorem edgeBudget_base (rows arity count depth bound : Nat) :
    edgeBudget rows arity count depth bound 0 = Operand.edgeBudget rows arity count depth bound := rfl

/-- The node recurrence follows operand, shorter tail, and query order. -/
theorem nodeBudget_step (rows arity count depth bound steps : Nat) :
    nodeBudget rows arity count depth bound (steps + 1) =
      Operand.nodeBudget rows arity count depth bound + nodeBudget rows arity count depth bound steps +
        Native.nodeBudget (max (operandRows rows count depth bound) (targetRows rows count depth bound steps)) (max arity 1) bound := rfl

/-- The edge recurrence uses its operand cost and the same conservative native Work limit. -/
theorem edgeBudget_step (rows arity count depth bound steps : Nat) :
    edgeBudget rows arity count depth bound (steps + 1) =
      Operand.edgeBudget rows arity count depth bound + edgeBudget rows arity count depth bound steps +
        Native.nodeBudget (max (operandRows rows count depth bound) (targetRows rows count depth bound steps)) (max arity 1) bound := rfl

/-- More additional operands cannot reduce the initial-only node budget. -/
theorem node_mono (rows arity count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    nodeBudget rows arity count depth bound first ≤ nodeBudget rows arity count depth bound last := foldNodes_mono _ _ _ _ enough

/-- More additional operands cannot reduce the initial-only edge budget. -/
theorem edge_mono (rows arity count depth bound : Nat) {first last : Nat} (enough : first ≤ last) :
    edgeBudget rows arity count depth bound first ≤ edgeBudget rows arity count depth bound last := foldEdges_mono _ _ _ _ enough

private theorem occurrences_parameters_mono (bound : Nat) {firstRows lastRows firstArity lastArity : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) :
    Occurrences.nodeCount firstRows firstArity bound ≤ Occurrences.nodeCount lastRows lastArity bound := by
  induction bound with
  | zero => exact Nat.le_refl _
  | succ bound ih => exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rows arity) ih) 1

private theorem operand_nodes_mono {firstRows lastRows firstArity lastArity firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    Operand.nodeBudget firstRows firstArity firstCount firstDepth firstBound ≤
      Operand.nodeBudget lastRows lastArity lastCount lastDepth lastBound := by
  have occurrences := Nat.le_trans (occurrences_parameters_mono firstBound rows arity)
    (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount_mono lastRows lastArity bound)
  have merged := Nat.le_trans
    (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.node_parameters_mono firstBound (forest_parameters_mono rows count depth) arity)
    (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.node_mono _ _ bound)
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul count occurrences) 1) merged

private theorem operand_edges_mono {firstRows lastRows firstArity lastArity firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    Operand.edgeBudget firstRows firstArity firstCount firstDepth firstBound ≤
      Operand.edgeBudget lastRows lastArity lastCount lastDepth lastBound :=
  Nat.le_trans
    (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edge_parameters_mono firstBound (forest_parameters_mono rows count depth) arity)
    (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edge_mono _ _ bound)

/-- Increasing any original forest limit retains the complete Target node budget. -/
theorem node_parameters_mono (steps : Nat)
    {firstRows lastRows firstArity lastArity firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    nodeBudget firstRows firstArity firstCount firstDepth firstBound steps ≤
      nodeBudget lastRows lastArity lastCount lastDepth lastBound steps :=
  foldNodes_parameters_mono steps (operand_nodes_mono rows arity count depth bound)
    (operandRows_mono rows count depth bound) (max_mono arity (Nat.le_refl 1)) bound

/-- Increasing any original forest limit retains the complete Target edge budget. -/
theorem edge_parameters_mono (steps : Nat)
    {firstRows lastRows firstArity lastArity firstCount lastCount firstDepth lastDepth firstBound lastBound : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) (count : firstCount ≤ lastCount)
    (depth : firstDepth ≤ lastDepth) (bound : firstBound ≤ lastBound) :
    edgeBudget firstRows firstArity firstCount firstDepth firstBound steps ≤
      edgeBudget lastRows lastArity lastCount lastDepth lastBound steps :=
  foldEdges_parameters_mono steps (operand_edges_mono rows arity count depth bound)
    (operandRows_mono rows count depth bound) (max_mono arity (Nat.le_refl 1)) bound

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
