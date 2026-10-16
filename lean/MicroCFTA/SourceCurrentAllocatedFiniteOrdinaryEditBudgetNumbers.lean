import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryValuePositions

/-!
# Fixed envelopes and literal edit resource sums

One edit uses fixed captured and current input profile limits.
Every literal position permits the same conservative leaf cost.
Ordinary node and edge occurrences pay for constructor reconstruction.
These bounds require no execution or returned profile.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
open Cache InternedBinderProtocol InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)
namespace Positions
export SourceCurrentAllocatedFiniteOrdinaryValuePositions (node children rows edge)
end Positions
namespace Occurrences
export SourceCurrentAllocatedFiniteOrdinaryOccurrences (node children rows edge)
end Occurrences
namespace Counts
export SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds (nodeCount edgeCount)
end Counts
local notation "Record" => SourceEqualityClassOrder.Record
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "TargetN" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget
local notation "TargetE" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget
local notation "Query" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget

/-- A fixed common row limit covers every leaf result and every retained input. -/
def outputRows (record : Record) (rows count depth bound inputRows : Nat) : Nat :=
  max (TargetRows record rows count depth bound) inputRows * max (TargetRows record rows count depth bound) inputRows

/-- The result arity covers captured targets, current inputs, and native sentinels. -/
def outputArity (arity inputArity : Nat) : Nat := max (max (max arity 1) inputArity) 1

/-- Current input rows fit the fixed result envelope, including a zero row limit. -/
theorem input_rows_le_outputRows (record : Record) (rows count depth bound inputRows : Nat) :
    inputRows ≤ outputRows record rows count depth bound inputRows :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_mul_self _)

/-- Current input arity fits the fixed result envelope. -/
theorem input_arity_le_outputArity (arity inputArity : Nat) : inputArity ≤ outputArity arity inputArity :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- Every position permits one complete first target and its native query. -/
def leafNodes (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat) : Nat :=
  TargetN rows arity count depth bound (record.paths.length - 1) +
    Query record rows arity count depth bound inputRows inputArity inputBound

/-- Edge headroom uses its target cost and the same conservative native Work bound. -/
def leafEdges (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat) : Nat :=
  TargetE rows arity count depth bound (record.paths.length - 1) +
    Query record rows arity count depth bound inputRows inputArity inputBound

/-- Every actual slot state fits the uniform first-force node cost. -/
theorem leaf_nodes_bound (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat)
    (before : SourceCurrentAllocatedSharedTargetState.State width) (path : EqualityNormalize.Path) :
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget
      record rows arity count depth bound inputRows inputArity inputBound before path ≤
      leafNodes record rows arity count depth bound inputRows inputArity inputBound := by
  cases present : before.targets path <;>
    simp [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget,
      SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, leafNodes, present]

/-- Every actual slot state fits the uniform first-force edge cost. -/
theorem leaf_edges_bound (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat)
    (before : SourceCurrentAllocatedSharedTargetState.State width) (path : EqualityNormalize.Path) :
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget
      record rows arity count depth bound inputRows inputArity inputBound before path ≤
      leafEdges record rows arity count depth bound inputRows inputArity inputBound := by
  cases present : before.targets path <;>
    simp [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget,
      SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, leafEdges, present]

private theorem max_mono {first last otherFirst otherLast : Nat}
    (one : first ≤ last) (other : otherFirst ≤ otherLast) : max first otherFirst ≤ max last otherLast :=
  Nat.max_le.mpr ⟨Nat.le_trans one (Nat.le_max_left _ _), Nat.le_trans other (Nat.le_max_right _ _)⟩

private theorem native_parameters_mono (bound : Nat) {firstRows lastRows firstArity lastArity : Nat}
    (rows : firstRows ≤ lastRows) (arity : firstArity ≤ lastArity) :
    SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget firstRows firstArity bound ≤
      SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget lastRows lastArity bound := by
  induction bound with
  | zero => exact Nat.le_refl _
  | succ bound ih =>
      exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul rows rows)
        (Nat.add_le_add_left (Nat.mul_le_mul arity ih) 1)) 1

/-- Widening the current input rows, arity, and height retains its uniform query cost. -/
theorem query_mono (record : Record) (rows arity count depth bound : Nat)
    {firstRows lastRows firstArity lastArity firstBound lastBound : Nat}
    (rowBound : firstRows ≤ lastRows) (arityBound : firstArity ≤ lastArity) (heightBound : firstBound ≤ lastBound) :
    Query record rows arity count depth bound firstRows firstArity firstBound ≤
      Query record rows arity count depth bound lastRows lastArity lastBound :=
  Nat.le_trans (native_parameters_mono (max bound firstBound)
    (max_mono (Nat.le_refl _) rowBound) (max_mono (Nat.le_refl _) arityBound))
    (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.node_mono _ _ (max_mono (Nat.le_refl _) heightBound))

/-- Fixed captured limits and wider current limits retain every uniform leaf node budget. -/
theorem leafNodes_mono (record : Record) (rows arity count depth bound : Nat)
    {firstRows lastRows firstArity lastArity firstBound lastBound : Nat}
    (rowBound : firstRows ≤ lastRows) (arityBound : firstArity ≤ lastArity) (heightBound : firstBound ≤ lastBound) :
    leafNodes record rows arity count depth bound firstRows firstArity firstBound ≤
      leafNodes record rows arity count depth bound lastRows lastArity lastBound :=
  Nat.add_le_add_left (query_mono record rows arity count depth bound rowBound arityBound heightBound) _

/-- Fixed captured limits and wider current limits retain every uniform leaf edge budget. -/
theorem leafEdges_mono (record : Record) (rows arity count depth bound : Nat)
    {firstRows lastRows firstArity lastArity firstBound lastBound : Nat}
    (rowBound : firstRows ≤ lastRows) (arityBound : firstArity ≤ lastArity) (heightBound : firstBound ≤ lastBound) :
    leafEdges record rows arity count depth bound firstRows firstArity firstBound ≤
      leafEdges record rows arity count depth bound lastRows lastArity lastBound :=
  Nat.add_le_add_left (query_mono record rows arity count depth bound rowBound arityBound heightBound) _

variable {Symbol Guard : Type}

/-- Each value position permits a leaf; each ordinary node permits reconstruction. -/
def nodeNodes (leaf : Nat) (value : Value Symbol Guard) : Nat := Positions.node value * leaf + (Occurrences.node value).1

/-- Each value position permits a leaf; each original edge permits reconstruction. -/
def nodeEdges (leaf : Nat) (value : Value Symbol Guard) : Nat := Positions.node value * leaf + (Occurrences.node value).2

/-- Forest node costs retain every repeated literal value position. -/
def childrenNodes (leaf : Nat) (values : List (Value Symbol Guard)) : Nat := Positions.children values * leaf + (Occurrences.children values).1

/-- Forest edge costs retain every repeated original row. -/
def childrenEdges (leaf : Nat) (values : List (Value Symbol Guard)) : Nat := Positions.children values * leaf + (Occurrences.children values).2

/-- Row node costs sum all original child forests. -/
def rowsNodes (leaf : Nat) (edges : List (EdgeValue Symbol Guard)) : Nat := Positions.rows edges * leaf + (Occurrences.rows edges).1

/-- Each row additionally permits its own edge reconstruction. -/
def rowsEdges (leaf : Nat) (edges : List (EdgeValue Symbol Guard)) : Nat := Positions.rows edges * leaf + (Occurrences.rows edges).2

/-- Empty contributes a leaf position but no ordinary reconstruction. -/
theorem node_empty (nodes edges : Nat) :
    nodeNodes nodes (.empty : Value Symbol Guard) = nodes ∧ nodeEdges edges (.empty : Value Symbol Guard) = edges := by
  simp [nodeNodes, nodeEdges, Positions.node, Occurrences.node]

/-- An ordinary node permits a root leaf, its child rows, and one node reconstruction. -/
theorem node_ordinary (nodes edgeCost : Nat) (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) :
    nodeNodes nodes (.node entry edges depth free) = nodes + 1 + rowsNodes nodes edges ∧
    nodeEdges edgeCost (.node entry edges depth free) = edgeCost + rowsEdges edgeCost edges := by
  simp only [nodeNodes, nodeEdges, rowsNodes, rowsEdges, Positions.node, Occurrences.node, Nat.add_mul, Nat.one_mul]
  constructor <;> omega

/-- An empty forest makes no leaf or constructor requests. -/
theorem children_nil (nodes edges : Nat) :
    childrenNodes nodes ([] : List (Value Symbol Guard)) = 0 ∧ childrenEdges edges ([] : List (Value Symbol Guard)) = 0 := by
  simp [childrenNodes, childrenEdges, Positions.children, Occurrences.children]

/-- A child cons retains additive costs in the original list order. -/
theorem children_cons (nodes edges : Nat) (first : Value Symbol Guard) (rest : List (Value Symbol Guard)) :
    childrenNodes nodes (first :: rest) = nodeNodes nodes first + childrenNodes nodes rest ∧
    childrenEdges edges (first :: rest) = nodeEdges edges first + childrenEdges edges rest := by
  simp only [childrenNodes, childrenEdges, nodeNodes, nodeEdges, Positions.children, Occurrences.children, Nat.add_mul]
  constructor <;> omega

/-- An empty row list makes no leaf or constructor requests. -/
theorem rows_nil (nodes edges : Nat) :
    rowsNodes nodes ([] : List (EdgeValue Symbol Guard)) = 0 ∧ rowsEdges edges ([] : List (EdgeValue Symbol Guard)) = 0 := by
  simp [rowsNodes, rowsEdges, Positions.rows, Occurrences.rows]

/-- A row adds its complete child forest and one edge reconstruction. -/
theorem rows_cons (nodes edges : Nat) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    rowsNodes nodes (first :: rest) = childrenNodes nodes first.children + rowsNodes nodes rest ∧
    rowsEdges edges (first :: rest) = 1 + childrenEdges edges first.children + rowsEdges edges rest := by
  cases first with
  | mk entry values =>
      simp only [rowsNodes, rowsEdges, childrenNodes, childrenEdges, Positions.rows, Positions.edge,
        Occurrences.rows, Occurrences.edge, EdgeValue.children, Nat.add_mul]
      constructor <;> omega

/-- Original node profile and height give an input-only bound for both edit sums. -/
theorem node_profile (nodes edges : Nat) (value : Value Symbol Guard) {rows arity : Nat}
    (profile : NodeShape rows arity value) (bound : Nat) (heightBound : height value ≤ bound) :
    nodeNodes nodes value ≤ (1 + arity * Counts.edgeCount rows arity bound) * nodes + Counts.nodeCount rows arity bound ∧
    nodeEdges edges value ≤ (1 + arity * Counts.edgeCount rows arity bound) * edges + Counts.edgeCount rows arity bound := by
  have positions := SourceCurrentAllocatedFiniteOrdinaryValuePositions.profile_node value profile bound heightBound
  have ordinary := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.node value profile bound heightBound
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right _ positions) ordinary.1,
    Nat.add_le_add (Nat.mul_le_mul_right _ positions) ordinary.2⟩

/-- A profiled forest's exact root count bounds both literal edit sums. -/
theorem children_profile (nodes edges : Nat) (values : List (Value Symbol Guard)) {rows arity : Nat}
    (profile : ChildrenShape rows arity values) (bound : Nat) (heightBound : childrenHeight values ≤ bound) :
    childrenNodes nodes values ≤ values.length * (1 + arity * Counts.edgeCount rows arity bound) * nodes +
        values.length * Counts.nodeCount rows arity bound ∧
    childrenEdges edges values ≤ values.length * (1 + arity * Counts.edgeCount rows arity bound) * edges +
        values.length * Counts.edgeCount rows arity bound := by
  have positions := SourceCurrentAllocatedFiniteOrdinaryValuePositions.profile_children values profile bound heightBound
  have ordinary := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right _ positions) ordinary.1,
    Nat.add_le_add (Nat.mul_le_mul_right _ positions) ordinary.2⟩

/-- A declared original forest length gives fixed budgets before any edit executes. -/
theorem forest_profile (nodes edges : Nat) (values : List (Value Symbol Guard)) {rows arity : Nat}
    (profile : ChildrenShape rows arity values) (count bound : Nat) (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound) :
    childrenNodes nodes values ≤ count * (1 + arity * Counts.edgeCount rows arity bound) * nodes + count * Counts.nodeCount rows arity bound ∧
    childrenEdges edges values ≤ count * (1 + arity * Counts.edgeCount rows arity bound) * edges + count * Counts.edgeCount rows arity bound := by
  have exactCount := children_profile nodes edges values profile bound heightBound
  constructor
  · exact Nat.le_trans exactCount.1 (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ lengthBound)) (Nat.mul_le_mul_right _ lengthBound))
  · exact Nat.le_trans exactCount.2 (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ lengthBound)) (Nat.mul_le_mul_right _ lengthBound))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
