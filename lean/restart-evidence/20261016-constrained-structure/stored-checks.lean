import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.NodeCertificate
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.NodeCertificate
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.EdgeCertificate
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.EdgeCertificate
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.Stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.Stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.lookupNode_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.lookupNode_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.lookupEdge_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.lookupEdge_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.demandNode_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.demandNode_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.demandEdge_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.demandEdge_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.finishNode_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.finishNode_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.finishEdge_stored
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.finishEdge_stored
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.node_observed_ready
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.node_observed_ready
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.edge_observed_ready
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.edge_observed_ready
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.node_started
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.node_started
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.edge_started
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored.edge_started

namespace FiniteOrdinaryStoredChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedFiniteOrdinaryStored
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "EdgeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {width : Nat} {Symbol Guard : Type}

theorem cold_publication_demand_and_machine_change
    (machine after : Machine Symbol Guard) (node : NodeRequest Symbol Guard) (edge : EdgeRequest Symbol Guard)
    (nodeHandle edgeHandle : Nat) :
    Stored (advance
      (demandEdge edgeHandle (lookupEdge width edge
        (demandNode nodeHandle (lookupNode width node (initial width machine)).2).2).2).2 after) := by
  have start := initial_stored width machine
  have publishedNode := lookupNode_stored _ node start
  have runningNode := demandNode_stored _ nodeHandle publishedNode
  have publishedEdge := lookupEdge_stored _ edge runningNode
  have runningEdge := demandEdge_stored _ edgeHandle publishedEdge
  exact advance_stored _ after runningEdge

theorem independent_node_and_edge_finish_keep_both_families
    (before : Native width Symbol Guard) (nodeHandle edgeHandle : Nat)
    (node : NodeRequest Symbol Guard) (edge : EdgeRequest Symbol Guard)
    (stored : Stored before)
    (nodeRunning : before.nodes.cells nodeHandle = some ⟨node, .evaluating⟩)
    (edgeRunning : before.edges.cells edgeHandle = some ⟨edge, .evaluating⟩)
    (entry : Interned (EdgeKey Symbol Guard)) :
    Stored (finishEdge edgeHandle ⟨entry, [.empty]⟩ (finishNode nodeHandle .empty before)) := by
  have nodeCertificate : NodeCertificate node (.empty : Value Symbol Guard) := by
    intro _ _ _
    exact ⟨.empty, Nat.zero_le _, Nat.zero_le _⟩
  have edgeCertificate : EdgeCertificate edge (⟨entry, [.empty]⟩ : EdgeValue Symbol Guard) := by
    intro _ _ _
    exact ⟨.cons .empty .nil, Nat.zero_le _, Nat.zero_le _⟩
  have nodeStored := finishNode_stored before nodeHandle node .empty stored nodeRunning nodeCertificate
  exact finishEdge_stored _ edgeHandle edge ⟨entry, [.empty]⟩ nodeStored edgeRunning edgeCertificate

theorem warm_node_hit_has_the_requested_minimum_height
    (request : NodeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after))
    (emptySeen : request.domain.key.seen = []) (left : NodeDomain request.left) (right : NodeDomain request.right) :
    NodeDomain result ∧ MergedOrdinaryHeight.height result ≤
      min (MergedOrdinaryHeight.height request.left) (MergedOrdinaryHeight.height request.right) ∧
      Stored after ∧ after = chosen ∧ Available after.machine.heap result := by
  obtain ⟨certificate, saved, same, available⟩ := node_observed_ready request before chosen after handle result
    physical stored ready safe selected demanded
  obtain ⟨domain, first, second⟩ := certificate emptySeen left right
  exact ⟨domain, Nat.le_min.mpr ⟨first, second⟩, saved, same, available⟩

theorem warm_edge_hit_bounds_every_returned_child
    (request : EdgeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after))
    (emptySeen : request.domain.key.seen = []) (left : EdgeDomain request.left) (right : EdgeDomain request.right) :
    Stored after ∧ after = chosen ∧ EdgeResident after.machine.heap result ∧
      ∀ child ∈ result.children, NodeDomain child ∧ MergedOrdinaryHeight.height child ≤
        min (MergedOrdinaryHeight.edgeHeight request.left) (MergedOrdinaryHeight.edgeHeight request.right) := by
  obtain ⟨certificate, saved, same, resident⟩ := edge_observed_ready request before chosen after handle result
    physical stored ready safe selected demanded
  obtain ⟨domain, first, second⟩ := certificate emptySeen left right
  refine ⟨saved, same, resident, ?_⟩
  intro child member
  have bound := SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge result child member
  exact ⟨domain.member child member, Nat.le_min.mpr ⟨Nat.le_trans bound first, Nat.le_trans bound second⟩⟩

theorem nonempty_seen_does_not_constrain_results
    (node : NodeRequest Symbol Guard) (edge : EdgeRequest Symbol Guard)
    (nodeSeen : node.domain.key.seen ≠ []) (edgeSeen : edge.domain.key.seen ≠ [])
    (nodeResult : Value Symbol Guard) (edgeResult : EdgeValue Symbol Guard) :
    NodeCertificate node nodeResult ∧ EdgeCertificate edge edgeResult :=
  ⟨fun emptySeen => False.elim (nodeSeen emptySeen), fun emptySeen => False.elim (edgeSeen emptySeen)⟩

end FiniteOrdinaryStoredChecks

#print axioms FiniteOrdinaryStoredChecks.cold_publication_demand_and_machine_change
#check @FiniteOrdinaryStoredChecks.cold_publication_demand_and_machine_change
#print axioms FiniteOrdinaryStoredChecks.independent_node_and_edge_finish_keep_both_families
#check @FiniteOrdinaryStoredChecks.independent_node_and_edge_finish_keep_both_families
#print axioms FiniteOrdinaryStoredChecks.warm_node_hit_has_the_requested_minimum_height
#check @FiniteOrdinaryStoredChecks.warm_node_hit_has_the_requested_minimum_height
#print axioms FiniteOrdinaryStoredChecks.warm_edge_hit_bounds_every_returned_child
#check @FiniteOrdinaryStoredChecks.warm_edge_hit_bounds_every_returned_child
#print axioms FiniteOrdinaryStoredChecks.nonempty_seen_does_not_constrain_results
#check @FiniteOrdinaryStoredChecks.nonempty_seen_does_not_constrain_results
