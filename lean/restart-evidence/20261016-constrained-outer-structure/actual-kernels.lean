import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual

namespace FiniteOrdinaryOuterActualChecks
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialChecks SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- One supplied call has the same physical, independent language, and structural return. -/
theorem same_node_return {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (inventory : Inventory)
    (checks : Checks (nodeCallTrace actual)) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧ Stored after ∧ NodeNarrow request.value result := by
  obtain ⟨next, post, resultAvailable, law⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver reads
    inventory checks initial inherited available
  exact ⟨next, post, resultAvailable, law, SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call formulas solver reads
    inventory checks initial inherited available domain stored⟩

/-- The first actual return supplies the second request's input domain, residency, complete context, and three certificates. -/
theorem generated_next_node {request : NodeRequest} {before middle after : Caller width} {firstValue result : Node}
    {first : NodeCall budget request before firstValue middle}
    {last : NodeCall budget ⟨request.inherited, firstValue⟩ middle result after} {memos current final : Memos}
    (firstReads : NodeCallReads formulas solver first memos current) (lastReads : NodeCallReads formulas solver last current final)
    (inventory : Inventory) (firstChecks : Checks (nodeCallTrace first)) (lastChecks : Checks (nodeCallTrace last))
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    ∃ next, Post formulas solver next before after final ∧ Stored after ∧ NodeNarrow request.value result := by
  obtain ⟨middleInventory, firstPost, firstAvailable, _⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver firstReads
    inventory firstChecks initial inherited available
  have firstBounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call formulas solver firstReads inventory firstChecks
    initial inherited available domain stored
  have nextInherited := inherited.grows firstPost.effects.grows.constraint_growth
  obtain ⟨next, lastPost, _, _⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver lastReads middleInventory lastChecks
    firstPost.context nextInherited firstAvailable
  have lastBounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call formulas solver lastReads middleInventory lastChecks
    firstPost.context nextInherited firstAvailable firstBounds.2.1 firstBounds.1
  exact ⟨next, firstPost.trans lastPost, lastBounds.1,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.node_trans firstBounds.2 lastBounds.2⟩

/-- Returned-edge descent bounds each literal child by the original input edge, even after parent narrowing. -/
theorem descendant_child_rank {inherited childInherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (inventory : Inventory)
    (checks : Checks (descendantsTrace actual)) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before)
    (child : Node) (member : child ∈ result.children) :
    DNode child ∧ SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨childInherited, child⟩ <
      SourceCurrentAllocatedPartialActiveOrder.edgeRank ⟨inherited, value⟩ := by
  have bounded := SourceCurrentAllocatedFiniteOrdinaryOuterActual.descendants formulas solver reads inventory checks initial
    inheritedReady resident domain stored
  have below := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited childInherited result child member
  have bound := bounded.2.2
  refine ⟨bounded.2.1.member child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at below ⊢
  omega

/-- Actual row results retain order, arity, domain, and their maximum original edge height. -/
theorem ordered_rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (inventory : Inventory)
    (checks : Checks (rowsTrace actual)) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before) :
    Stored after ∧ DRows results ∧ results.length = values.length ∧
      MergedOrdinaryHeight.edgesHeight results ≤ MergedOrdinaryHeight.edgesHeight values := by
  have bounded := SourceCurrentAllocatedFiniteOrdinaryOuterActual.rows formulas solver reads inventory checks initial
    inheritedReady available domain stored
  exact ⟨bounded.1, SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_domain bounded.2, bounded.2.length_eq.symm,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_height bounded.2⟩

/-- Contradiction skips every actual child call and needs no machine range premise. -/
theorem contradictory_children (budget : Nat) (inventory : Inventory) (values : List Node) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints .contradiction)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Stored before ∧ All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  let actual : Children budget .contradiction values before (EqualityLeafProjectionRuntimeEmpty.erase values) before := .contradiction
  have reads : ChildrenReads formulas solver actual memos memos := .contradiction
  have checks : Checks (childrenTrace actual) := by
    intro request first result after body reached
    cases reached with
    | step direct _ => cases direct
  exact SourceCurrentAllocatedFiniteOrdinaryOuterActual.children formulas solver reads inventory checks initial inherited available domain stored

#print axioms same_node_return
#check @same_node_return
#print axioms generated_next_node
#check @generated_next_node
#print axioms descendant_child_rank
#check @descendant_child_rank
#print axioms ordered_rows
#check @ordered_rows
#print axioms contradictory_children
#check @contradictory_children
end FiniteOrdinaryOuterActualChecks
