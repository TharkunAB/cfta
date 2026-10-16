import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers

namespace MicroCFTA.EditBudgetNumberChecks
open Cache InternedBinderProtocol InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape RowsShape EdgeShape)
open MergedOrdinaryHeight (height childrenHeight edgesHeight edgeHeight)

/-- Repeated literal children and rows contribute separately even when all records share identities. -/
theorem repeated_literal_cost (nodes edgeCost : Nat) (nodeEntry : Interned NodeKey)
    (edgeEntry : Interned (EdgeKey Symbol Guard)) :
    let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
    let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
    nodeNodes nodes value = 5 * nodes + 1 ∧ nodeEdges edgeCost value = 5 * edgeCost + 2 := by
  constructor <;> rfl

/-- Smaller current input limits in any slot state fit the original edit's fixed leaf budget. -/
theorem descendant_leaf_cost (record : SourceEqualityClassOrder.Record) (rows arity count depth bound : Nat)
    (before : SourceCurrentAllocatedSharedTargetState.State width) (path : EqualityNormalize.Path)
    {localRows wholeRows localArity wholeArity localHeight wholeHeight : Nat}
    (rowBound : localRows ≤ wholeRows) (arityBound : localArity ≤ wholeArity) (heightBound : localHeight ≤ wholeHeight) :
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget record rows arity count depth bound
      localRows localArity localHeight before path ≤ leafNodes record rows arity count depth bound wholeRows wholeArity wholeHeight ∧
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget record rows arity count depth bound
      localRows localArity localHeight before path ≤ leafEdges record rows arity count depth bound wholeRows wholeArity wholeHeight :=
  ⟨Nat.le_trans (leaf_nodes_bound record rows arity count depth bound localRows localArity localHeight before path)
      (leafNodes_mono record rows arity count depth bound rowBound arityBound heightBound),
    Nat.le_trans (leaf_edges_bound record rows arity count depth bound localRows localArity localHeight before path)
      (leafEdges_mono record rows arity count depth bound rowBound arityBound heightBound)⟩

/-- Original row, arity, height, and root limits bound the full repeated forest before any edit. -/
theorem profiled_repeated_forest (nodes edgeCost : Nat) (nodeEntry : Interned NodeKey)
    (edgeEntry : Interned (EdgeKey Symbol Guard)) :
    let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
    let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
    childrenNodes nodes [value, value] ≤ 10 * nodes + 2 ∧ childrenEdges edgeCost [value, value] ≤ 10 * edgeCost + 4 := by
  let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
  let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
  have profile : ChildrenShape 2 2 [value, value] := by
    simp [value, row, ChildrenShape, NodeShape, RowsShape, EdgeShape]
  have bounded : childrenHeight [value, value] ≤ 1 := by
    simp [value, row, childrenHeight, height, edgesHeight, edgeHeight]
  have result := forest_profile nodes edgeCost [value, value] profile 2 1 (by simp) bounded
  simpa only [Counts.nodeCount, Counts.edgeCount] using result

#print axioms repeated_literal_cost
#check @repeated_literal_cost
#print axioms descendant_leaf_cost
#check @descendant_leaf_cost
#print axioms profiled_repeated_forest
#check @profiled_repeated_forest
end MicroCFTA.EditBudgetNumberChecks
