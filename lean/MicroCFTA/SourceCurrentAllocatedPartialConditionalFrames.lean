import MicroCFTA.SourceCurrentAllocatedPartialConditionalActive
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames

/-!
# Filtered ancestor bounds after actual completed outer prefixes

A completed prefix leaves no new evaluating owner. Its complete stored
requests retain the same Region and plain-edge tests. These theorems consume
an earlier completed prefix. They do not assume or construct a future call.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalFrames
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveFrames (NoNewActive)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- Lowering the bound retains every filtered evaluating-owner inequality. -/
theorem active_mono {small bound : Nat} {before : Caller width}
    (active : ActiveAbove bound before) (below : small ≤ bound) : ActiveAbove small before :=
  ⟨fun handle owner found plain => Nat.lt_of_le_of_lt below (active.nodes handle owner found plain),
    fun handle owner found plain => Nat.lt_of_le_of_lt below (active.edges handle owner found plain)⟩

/-- No-new-active retention transports the same static owner filters and bound. -/
theorem active_above {before after : Caller width} (frame : NoNewActive before after)
    {bound : Nat} (active : ActiveAbove bound before) : ActiveAbove bound after :=
  ⟨fun handle owner found plain => active.nodes handle owner (frame.nodes handle owner found) plain,
    fun handle owner found plain => active.edges handle owner (frame.edges handle owner found) plain⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A completed node call restores every earlier filtered ancestor bound. -/
theorem node_call {budget bound : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeCall budget request before result after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.node_call actual) active

/-- A completed node body retains earlier filtered ancestors. -/
theorem node_body {budget bound : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeBody budget request before result after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.node_body actual) active

/-- A completed edge call removes its own evaluating phase before the next prefix. -/
theorem edge_call {budget bound : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.edge_call actual) active

/-- An actual parent body retains the filtered bound at the same returned caller. -/
theorem edge_body {budget bound : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeBody budget request before result after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.edge_body actual) active

/-- Ordered completed rows retain the filtered ancestor bound. -/
theorem rows {budget bound : Nat} {inherited : EqValue} {before after : Caller width} {values results : List Edge}
    (actual : Rows budget inherited values before results after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.rows actual) active

/-- Completed descendants retain the filtered bound through their actual rebuilding. -/
theorem descendants {budget bound : Nat} {inherited : EqValue} {before after : Caller width} {value result : Edge}
    (actual : Descendants budget inherited value before result after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.descendants actual) active

/-- Both completed children branches retain earlier filtered ancestors. -/
theorem children {budget bound : Nat} {combined : EqValue} {before after : Caller width} {values results : List Node}
    (actual : Children budget combined values before results after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.children actual) active

/-- A completed indexed walk retains the filtered ancestor bound before its suffix. -/
theorem walk {budget bound : Nat} {combined : EqValue} {index : Nat} {before after : Caller width} {values results : List Node}
    (actual : Walk budget combined index values before results after) (active : ActiveAbove bound before) : ActiveAbove bound after :=
  active_above (SourceCurrentAllocatedPartialActiveFrames.walk actual) active

end MicroCFTA.SourceCurrentAllocatedPartialConditionalFrames
