import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite

namespace ProfileBudgetIntegration
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Uniform node headroom applies before completion at every actual raw prefix. -/
theorem node_uniform_prefix (bits rows arity bound : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Node) (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (MergedOrdinaryHeight.height left) (MergedOrdinaryHeight.height right) ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget rows arity bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + nodeBudget rows arity bound ≤ 2 ^ (bits + 2))
    (fuel : Nat) (next : Control Node) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestNode emptyDomain left right)) before next after) :
    Capacity bits after ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget rows arity bound ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + nodeBudget rows arity bound := by
  have bounded := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.node_budget_le left right leftShape rightShape bound heights
  have leftDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain left leftShape
  have rightDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain right rightShape
  have prefixCapacity := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_capacity bits before good left right
    leftAvailable rightAvailable leftDomain rightDomain (by omega) (by omega) fuel next after actual
  have supplies := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.node_prefix_budget bits before good left right
    leftAvailable rightAvailable leftDomain rightDomain ⟨by omega, by omega⟩ fuel next after actual
  exact ⟨prefixCapacity, by omega, by omega⟩

/-- Uniform edge headroom applies at raw prefixes, including a rejected sentinel branch. -/
theorem edge_uniform_prefix (bits rows arity bound : Nat) (before : Checked (bits + 2)) (good : Good before)
    (left right : Edge) (leftResident : EdgeResident before.native.machine.heap left)
    (rightResident : EdgeResident before.native.machine.heap right)
    (leftShape : EdgeShape rows arity left) (rightShape : EdgeShape rows arity right)
    (heights : max (MergedOrdinaryHeight.edgeHeight left) (MergedOrdinaryHeight.edgeHeight right) ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + edgeBudget rows arity bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget rows arity bound ≤ 2 ^ (bits + 2))
    (fuel : Nat) (next : Control Edge) (after : Checked (bits + 2))
    (actual : Steps fuel (.code (requestEdge emptyDomain left right)) before next after) :
    Capacity bits after ∧
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + edgeBudget rows arity bound ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget rows arity bound := by
  have bounded := SourceCurrentAllocatedFiniteOrdinaryProfileBudget.edge_budget_le left right leftShape rightShape bound heights
  have leftDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.domain left leftShape
  have rightDomain := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.domain right rightShape
  have prefixCapacity := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edge_prefix_capacity bits before good left right
    leftResident rightResident leftDomain rightDomain (by omega) (by omega) fuel next after actual
  have supplies := SourceCurrentAllocatedFiniteOrdinaryNativeBudget.edge_prefix_budget bits before good left right
    leftResident rightResident leftDomain rightDomain ⟨by omega, by omega⟩ fuel next after actual
  exact ⟨prefixCapacity, by omega, by omega⟩

end ProfileBudgetIntegration

#print axioms ProfileBudgetIntegration.node_uniform_prefix
#check @ProfileBudgetIntegration.node_uniform_prefix

#print axioms ProfileBudgetIntegration.edge_uniform_prefix
#check @ProfileBudgetIntegration.edge_uniform_prefix
