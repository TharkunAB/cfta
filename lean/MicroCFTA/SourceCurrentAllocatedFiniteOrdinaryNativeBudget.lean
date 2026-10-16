import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution

/-!
# Input-derived constructor budgets for native ordinary queries

The original operand records determine row, arity, and height limits.
The whole expansion budget includes every repeated source occurrence.
Every finite actual yielded prefix fits that initial budget.
No completed query, future capacity, or actual-request bound is an input.
The two constructor supplies remain separate from other runtime resources.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (requestsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain

/-- The original node operands determine a static bound on all constructor requests. -/
def nodeBudget (left right : Node) : Nat :=
  let limits := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.childrenLimits [left, right]
  SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.nodeCost limits.1 limits.2 ⟨emptyDomain, left, right⟩

/-- The original edge operands determine a static bound on all constructor requests. -/
def edgeBudget (left right : Edge) : Nat :=
  let limits := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.rowsLimits [left, right]
  SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.edgeCost limits.1 limits.2 ⟨emptyDomain, left, right⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial physical facts and operand syntax bound every finite actual node-query prefix. -/
theorem node_prefix_budget (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Node)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right)
    (capacity : Capacity bits before) (fuel : Nat) (next : Control Node) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode emptyDomain left right)) before next after) :
    nodeRequests (requestsThrough fuel (.code (requestNode emptyDomain left right)) before) +
      edgeRequests (requestsThrough fuel (.code (requestNode emptyDomain left right)) before) ≤ nodeBudget left right ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget left right ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + nodeBudget left right := by
  let limits := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.childrenLimits [left, right]
  have shapes : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape limits.1 limits.2 [left, right] :=
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.children_shape_self [left, right] (.cons leftDomain (.cons rightDomain .nil))
  have codeBound := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.request_node limits.1 limits.2
    ⟨emptyDomain, left, right⟩ ⟨rfl, shapes.1, shapes.2.1⟩
  have leftKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
    good.native.machine.1.coherent good.native.machine.1.linked capacity.1 capacity.2 left leftAvailable leftDomain
  have rightKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_available bits before.native.machine.heap
    good.native.machine.1.coherent good.native.machine.1.linked capacity.1 capacity.2 right rightAvailable rightDomain
  have certificate : SourceCurrentAllocatedFiniteOrdinaryWordExecution.Certified bits before.native.machine
      (.code (requestNode emptyDomain left right)) :=
    SourceCurrentAllocatedFiniteOrdinaryWordCode.request_node bits before.native.machine
      ⟨emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftAvailable, rightAvailable⟩
  have origins := SourceCurrentAllocatedFiniteOrdinaryWordExecution.Origins.of_valid before.native good.native
  obtain ⟨remaining, finalBound, spent⟩ := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution.prefix_bound
    (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.scheme limits.1 limits.2)
    (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.node_bound limits.1 limits.2)
    (fun {_A} request resume {_width} before after next tail inputs continuation one =>
      SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.body_bound limits.1 limits.2 request inputs resume before after next tail continuation one)
    bits before.native.machine good.native.machine fuel (.code (requestNode emptyDomain left right)) next
    before after (nodeBudget left right) origins certificate codeBound actual
  have reserved := SourceCurrentAllocatedFiniteOrdinaryQueryReservations.prefix_bounds bits before.native.machine good.native.machine
    fuel (.code (requestNode emptyDomain left right)) next before after origins certificate actual
  exact ⟨by omega, by omega, by omega⟩

/-- Initial supplies plus the computed node budget derive capacity at every actual yielded prefix. -/
theorem node_prefix_capacity (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Node)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget left right ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + nodeBudget left right ≤ 2 ^ (bits + 2))
    (fuel : Nat) (next : Control Node) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode emptyDomain left right)) before next after) : Capacity bits after := by
  have initial : Capacity bits before := ⟨by omega, by omega⟩
  have bounded := node_prefix_budget bits before good left right leftAvailable rightAvailable
    leftDomain rightDomain initial fuel next after actual
  exact ⟨Nat.le_trans bounded.2.1 nodes, Nat.le_trans bounded.2.2 edges⟩

/-- Initial physical facts and operand syntax bound every finite actual edge-query prefix. -/
theorem edge_prefix_budget (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Edge)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftDomain : DEdge left) (rightDomain : DEdge right)
    (capacity : Capacity bits before) (fuel : Nat) (next : Control Edge) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestEdge emptyDomain left right)) before next after) :
    nodeRequests (requestsThrough fuel (.code (requestEdge emptyDomain left right)) before) +
      edgeRequests (requestsThrough fuel (.code (requestEdge emptyDomain left right)) before) ≤ edgeBudget left right ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + edgeBudget left right ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget left right := by
  let limits := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.rowsLimits [left, right]
  have shapes : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.RowsShape limits.1 limits.2 [left, right] :=
    SourceCurrentAllocatedFiniteOrdinaryNativeProfile.rows_shape_self [left, right] (.cons leftDomain (.cons rightDomain .nil))
  have codeBound := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.request_edge limits.1 limits.2
    ⟨emptyDomain, left, right⟩ ⟨rfl, shapes.1, shapes.2.1⟩
  have leftKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_resident bits before.native.machine.heap
    good.native.machine.1 capacity.1 capacity.2 left leftResident leftDomain
  have rightKeys := SourceCurrentAllocatedFiniteOrdinaryKeys.of_resident bits before.native.machine.heap
    good.native.machine.1 capacity.1 capacity.2 right rightResident rightDomain
  have certificate : SourceCurrentAllocatedFiniteOrdinaryWordExecution.Certified bits before.native.machine
      (.code (requestEdge emptyDomain left right)) :=
    SourceCurrentAllocatedFiniteOrdinaryWordCode.request_edge bits before.native.machine
      ⟨emptyDomain, left, right⟩ ⟨rfl, leftKeys, rightKeys, leftResident, rightResident⟩
  have origins := SourceCurrentAllocatedFiniteOrdinaryWordExecution.Origins.of_valid before.native good.native
  obtain ⟨remaining, finalBound, spent⟩ := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution.prefix_bound
    (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.scheme limits.1 limits.2)
    (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.node_bound limits.1 limits.2)
    (fun {_A} request resume {_width} before after next tail inputs continuation one =>
      SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.body_bound limits.1 limits.2 request inputs resume before after next tail continuation one)
    bits before.native.machine good.native.machine fuel (.code (requestEdge emptyDomain left right)) next
    before after (edgeBudget left right) origins certificate codeBound actual
  have reserved := SourceCurrentAllocatedFiniteOrdinaryQueryReservations.prefix_bounds bits before.native.machine good.native.machine
    fuel (.code (requestEdge emptyDomain left right)) next before after origins certificate actual
  exact ⟨by omega, by omega, by omega⟩

/-- Initial supplies plus the computed edge budget derive capacity at every actual yielded prefix. -/
theorem edge_prefix_capacity (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Edge)
    (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftDomain : DEdge left) (rightDomain : DEdge right)
    (nodes : before.native.machine.heap.nodes.next + edgeBudget left right ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget left right ≤ 2 ^ (bits + 2))
    (fuel : Nat) (next : Control Edge) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestEdge emptyDomain left right)) before next after) : Capacity bits after := by
  have initial : Capacity bits before := ⟨by omega, by omega⟩
  have bounded := edge_prefix_budget bits before good left right leftResident rightResident
    leftDomain rightDomain initial fuel next after actual
  exact ⟨Nat.le_trans bounded.2.1 nodes, Nat.le_trans bounded.2.2 edges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget
