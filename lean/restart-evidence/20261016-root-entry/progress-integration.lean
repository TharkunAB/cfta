import MicroCFTA.SourceCurrentAllocatedPartialActiveOrder
import MicroCFTA.SourceCurrentAllocatedPartialDescent

namespace MicroCFTA.PartialActiveOrderIndependentProbes
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialActiveOrder
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

-- Cold outer tables preserve every lower warm component and derive both structural invariants.
example (bound : Nat) (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ActiveAbove bound (initial checked merge fourth) ∧ ReturnedBounds (initial checked merge fourth) ∧
    (initial checked merge fourth).checked = checked ∧ (initial checked merge fourth).merge = merge ∧
    (initial checked merge fourth).fourth = fourth :=
  ⟨initial_above bound checked merge fourth, initial_bounds checked merge fourth, rfl, rfl, rfl⟩

-- An actual ordinary-node start admits the exact original row request below it.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inherited : EqValue)
    (entry) (edges : List Edge) (depth free) (edge : Edge) (member : edge ∈ edges)
    (before running : Caller width) (handle : Nat) (owner : NodeRequest)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (ready : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Available before.checked.native.machine.heap (.node entry edges depth free))
    (active : ActiveAbove (nodeRank ⟨inherited, .node entry edges depth free⟩) before)
    (started : beginNode ⟨inherited, .node entry edges depth free⟩ before = (handle, .evaluate owner, running)) :
    ActiveAbove (edgeRank ⟨inherited, edge⟩) running :=
  node_push formulas solver sound coherent ready available active
    (edge_lt_node inherited entry edges depth free edge member) started

-- Indexed equality allocation retains every active owner, even when it allocates a new payload identity.
example {bound : Nat} {nodeSkip edgeSkip : Option Nat} {before : Caller width}
    (active : ActiveExcept bound nodeSkip edgeSkip before) (combined : EqValue) (index : Nat) :
    ActiveExcept bound nodeSkip edgeSkip (SourceCurrentAllocatedPartialGraph.descend before combined index).2 := by
  change ActiveExcept bound nodeSkip edgeSkip (advance before _ before.fourth before.merge)
  exact active.advance _ _ _

-- Literal node begin then finish restores the original ancestor bound without a future body premise.
example {bound : Nat} (request : NodeRequest) (before : Caller width) (result : Node)
    (active : ActiveAbove bound before) :
    ActiveAbove bound (finishNode (beginNode request before).1 result (beginNode request before).2.2) :=
  finishNode_above result (beginNode_except request before active)

-- The independent edge family has the same actual owner restoration.
example {bound : Nat} (request : EdgeRequest) (before : Caller width) (result : Edge)
    (active : ActiveAbove bound before) :
    ActiveAbove bound (finishEdge (beginEdge request before).1 result (beginEdge request before).2.2) :=
  finishEdge_above result (beginEdge_except request before active)

-- A stored returned edge with original-or-erased children yields strict next-node descent.
example {before : Caller width} (bounds : ReturnedBounds before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (shape : result.children = owner.value.children ∨
      result.children = owner.value.children.map (fun _ => .empty))
    (childInherited : EqValue) {child : Node} (member : child ∈ result.children) :
    ReturnedBounds (finishEdge handle result before) ∧ nodeRank ⟨childInherited, child⟩ < edgeRank owner := by
  have after := bounds.finishEdge result running (original_or_erased_bound owner.value result shape)
  exact ⟨after, returned_child_lt after (finishEdge_returned handle owner result before running) childInherited member⟩

-- Actual child membership gives a rank independent of the next inherited allocation.
example (first second third : EqValue) (edge : Edge) (child : Node) (member : child ∈ edge.children) :
    nodeRank ⟨first, child⟩ < edgeRank ⟨second, edge⟩ ∧
      nodeRank ⟨third, child⟩ = nodeRank ⟨first, child⟩ :=
  ⟨child_lt_edge second first edge child member, rfl⟩

-- Coherent resident aliases preserve a candidate's node rank without comparing its payload syntax.
example (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (first second : NodeRequest)
    (one : Available heap first.value) (two : Available heap second.value) (same : first.key = second.key) :
    rank (.inl first) = rank (.inl second) := nodeRank_of_key heap coherent first second one two same

-- Coherent resident aliases preserve the separate edge request rank.
example (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (first second : EdgeRequest)
    (one : EdgeResident heap first.value) (two : EdgeResident heap second.value) (same : first.key = second.key) :
    rank (.inr first) = rank (.inr second) := edgeRank_of_key heap coherent first second one two same

-- Natural rank descent gives accessibility without a finite carrier of allocated keys.
example (request : Sum NodeRequest EdgeRequest) : Acc (fun child parent => rank child < rank parent) request :=
  wellFounded.apply request

end MicroCFTA.PartialActiveOrderIndependentProbes
