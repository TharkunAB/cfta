import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudget

namespace NativeBudgetIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A completed native return retains the initial static budget at its exact returned state. -/
theorem completed_node_budget (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Node) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) (leftDomain : DNode left) (rightDomain : DNode right)
    (initial : Capacity bits before) (fuel : Nat) (result : Node) (after : Checked (bits + 2))
    (done : execute fuel (.code (requestNode emptyDomain left right)) before = .done result after) :
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right := by
  obtain ⟨steps, _shorter, trace⟩ := done_trace fuel (.code (requestNode emptyDomain left right)) before after result done
  exact (SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_budget bits before good left right first second leftDomain rightDomain
    initial steps (.code (.pure result)) after trace).2

/-- A completed native return retains the initial static budget at its exact returned state. -/
theorem completed_edge_budget (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Edge) (first : EdgeResident before.native.machine.heap left)
    (second : EdgeResident before.native.machine.heap right) (leftDomain : DEdge left) (rightDomain : DEdge right)
    (initial : Capacity bits before) (fuel : Nat) (result : Edge) (after : Checked (bits + 2))
    (done : execute fuel (.code (requestEdge emptyDomain left right)) before = .done result after) :
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edgeBudget left right ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edgeBudget left right := by
  obtain ⟨steps, _shorter, trace⟩ := done_trace fuel (.code (requestEdge emptyDomain left right)) before after result done
  exact (SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edge_prefix_budget bits before good left right first second leftDomain rightDomain
    initial steps (.code (.pure result)) after trace).2

/-- Resuming an actual prefix retains the original budget instead of starting a fresh budget. -/
theorem resumed_node_capacity (bits : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Node) (first : Available before.native.machine.heap left) (second : Available before.native.machine.heap right)
    (leftDomain : DNode left) (rightDomain : DNode right)
    (nodes : before.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudget.nodeBudget left right ≤ 2 ^ (bits + 2))
    (firstCount restCount : Nat) (middle next : Control Node) (current after : Checked (bits + 2))
    (earlier : Steps firstCount (.code (requestNode emptyDomain left right)) before middle current)
    (later : Steps restCount middle current next after) : Capacity bits after := by
  exact SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_capacity bits before good left right first second leftDomain rightDomain nodes edges
    (firstCount + restCount) next after (Steps.trans firstCount restCount _ middle next before current after earlier later)

end NativeBudgetIntegration

#print axioms NativeBudgetIntegration.completed_node_budget
#check @NativeBudgetIntegration.completed_node_budget

#print axioms NativeBudgetIntegration.completed_edge_budget
#check @NativeBudgetIntegration.completed_edge_budget

#print axioms NativeBudgetIntegration.resumed_node_capacity
#check @NativeBudgetIntegration.resumed_node_capacity
