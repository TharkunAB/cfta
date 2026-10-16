import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRawReads
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow

namespace FiniteOrdinaryRawReadsChecks
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
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
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {bits budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- A raw call derives its own strict reads, checks, full postcondition, and structural law. -/
theorem same_node_return {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    (actual : NodeCall budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : DNode request.value) (stored : Stored before)
    (plan : Plan bits budget (.nodeCall request before)) :
    ∃ final next, NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      Stored after ∧ NodeNarrow request.value result ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.node_call bits formulas solver actual
    inventory initial inherited available domain stored plan
  obtain ⟨checks, next, post, resultAvailable, resultStored, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver reads inventory initial
      inherited available domain stored
  exact ⟨final, next, reads, checks, post, resultAvailable, resultStored, narrow, law⟩

/-- The first raw result derives the second call's context, input domain, and three cache certificates. -/
theorem generated_next_node {request : NodeRequest} {before middle after : Caller (bits + 2)} {firstValue result : Node}
    (first : NodeCall budget request before firstValue middle)
    (last : NodeCall budget ⟨request.inherited, firstValue⟩ middle result after)
    (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : DNode request.value) (stored : Stored before)
    (firstPlan : Plan bits budget (.nodeCall request before))
    (lastPlan : Plan bits budget (.nodeCall ⟨request.inherited, firstValue⟩ middle)) :
    ∃ current final next, NodeCallReads formulas solver first memos current ∧
      NodeCallReads formulas solver last current final ∧
      Post formulas solver next before after final ∧ Stored after ∧ NodeNarrow request.value result := by
  obtain ⟨current, firstReads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.node_call bits formulas solver first
    inventory initial inherited available domain stored firstPlan
  obtain ⟨_checks, middleInventory, firstPost, firstAvailable, firstStored, firstBounds, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver firstReads inventory initial
      inherited available domain stored
  have nextInherited := inherited.grows firstPost.effects.grows.constraint_growth
  obtain ⟨final, lastReads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.node_call bits formulas solver last
    middleInventory firstPost.context nextInherited firstAvailable firstBounds.1 firstStored lastPlan
  obtain ⟨_lastChecks, next, lastPost, _lastAvailable, lastStored, lastBounds, _lastLaw⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver lastReads middleInventory
      firstPost.context nextInherited firstAvailable firstBounds.1 firstStored
  exact ⟨current, final, next, firstReads, lastReads, firstPost.trans lastPost, lastStored,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.node_trans firstBounds lastBounds⟩

/-- The actual row sequence derives all global reads and preserves positional edge bounds. -/
theorem ordered_rows {inherited : EqValue} {values results : List Edge} {before after : Caller (bits + 2)}
    (actual : Rows budget inherited values before results after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before)
    (plan : Plan bits budget (.rows inherited values before)) :
    ∃ final next, RowsReads formulas solver actual memos final ∧ Post formulas solver next before after final ∧
      Stored after ∧ DRows results ∧ results.length = values.length ∧
      MergedOrdinaryHeight.edgesHeight results ≤ MergedOrdinaryHeight.edgesHeight values := by
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.rows bits formulas solver actual
    inventory initial inheritedReady resident domain stored plan
  obtain ⟨_checks, next, post, _resident, resultStored, narrow, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.rows formulas solver reads inventory initial
      inheritedReady resident domain stored
  exact ⟨final, next, reads, post, resultStored, SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_domain narrow,
    narrow.length_eq.symm, SourceCurrentAllocatedFiniteOrdinaryNarrow.rows_height narrow⟩

/-- Descendant reads derive a strict input-edge rank bound for every actual returned child. -/
theorem descendant_child_rank {inherited childInherited : EqValue} {value result : Edge}
    {before after : Caller (bits + 2)}
    (actual : Descendants budget inherited value before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before)
    (plan : Plan bits budget (.descendants inherited value before)) (child : Node) (member : child ∈ result.children) :
    DNode child ∧ SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨childInherited, child⟩ <
      SourceCurrentAllocatedPartialActiveOrder.edgeRank ⟨inherited, value⟩ := by
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.descendants bits formulas solver actual
    inventory initial inheritedReady resident domain stored plan
  obtain ⟨_checks, _next, _post, _resident, _stored, bounded, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants formulas solver reads inventory initial
      inheritedReady resident domain stored
  have below := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited childInherited result child member
  have bound := bounded.2
  refine ⟨bounded.1.member child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at below ⊢
  omega

/-- The contradiction branch constructs reads without any child-call receipt or machine check. -/
theorem contradictory_children (inventory : Inventory) (values : List Node) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints .contradiction)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before)
    (plan : Plan bits budget (.children .contradiction values before)) :
    ∃ final, ChildrenReads formulas solver
      (Children.contradiction (budget := budget) (before := before) (values := values)) memos final ∧ final = memos := by
  let actual : Children budget .contradiction values before (EqualityLeafProjectionRuntimeEmpty.erase values) before := .contradiction
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterRawReads.children bits formulas solver actual
    inventory initial inherited available domain stored plan
  exact ⟨final, reads, SourceCurrentAllocatedPartialSourceReads.children_contradiction reads⟩

#print axioms same_node_return
#check @same_node_return
#print axioms generated_next_node
#check @generated_next_node
#print axioms ordered_rows
#check @ordered_rows
#print axioms descendant_child_rank
#check @descendant_child_rank
#print axioms contradictory_children
#check @contradictory_children
end FiniteOrdinaryRawReadsChecks
