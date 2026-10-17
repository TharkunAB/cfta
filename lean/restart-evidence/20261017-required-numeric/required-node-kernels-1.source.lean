import MicroCFTA.SourceCurrentConstrainedCapRequiredNumeric
import MicroCFTA.SourceCurrentRequiredSupport
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.RequiredNodeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredGraph SourceEqualityNeeded
open SourceCurrentRequiredSupport
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentConstrainedCap (Cap)

private def leafEdge := run (makeEdge (Symbol := Nat) 0 true []) empty
private def leafNode := run (makeNode [leafEdge.1]) leafEdge.2
private def openEdge := run (makeEdge 1 false [leafNode.1, .reference .depth]) leafNode.2
private def openNode := run (makeNode [openEdge.1]) openEdge.2
private def heap := openNode.2
private def value := openNode.1
private def needed : Needed := .node [(0, .node [])]

private theorem empty_semantic : SemanticReady (empty (Symbol := Nat) (Guard := Bool)) :=
  SourceEqualityRequiredSemanticCache.constructed .empty .empty empty (by simp only [InternedFreshOrdinaryConstruction.build])
private theorem leaf_edge :
    SourceEqualityRequiredCache.Keeps empty leafEdge.2 ∧
      InternedEdgeResidency.EdgeResident leafEdge.2 leafEdge.1 ∧ leafEdge.1.children = [] :=
  SourceEqualityRequiredCache.edge 0 true [] empty empty_semantic.ready (by intro _ member; cases member)
private theorem leaf_semantic : SemanticReady leafNode.2 :=
  (SourceEqualityOpenOrdinaryHead.node [leafEdge.1] leafEdge.2
    (SourceEqualityRequiredSemanticCache.edge 0 true [] empty empty_semantic (by intro _ member; cases member))
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ leaf_edge.2.1)).2.1
private theorem leaf_available : Available leafNode.2 leafNode.1 :=
  (SourceEqualityOpenOrdinaryHead.node [leafEdge.1] leafEdge.2
    (SourceEqualityRequiredSemanticCache.edge 0 true [] empty empty_semantic (by intro _ member; cases member))
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ leaf_edge.2.1)).2.2.1
private theorem open_inputs : Values leafNode.2 [leafNode.1, .reference .depth] := by
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact leaf_available
  · exact InternedNestedProvenance.depth_available _
private theorem open_edge : SourceEqualityRequiredCache.Keeps leafNode.2 openEdge.2 ∧
    InternedEdgeResidency.EdgeResident openEdge.2 openEdge.1 ∧
      openEdge.1.children = [leafNode.1, .reference .depth] :=
  SourceEqualityRequiredCache.edge 1 false _ leafNode.2 leaf_semantic.ready open_inputs
private theorem source_semantic : SemanticReady heap :=
  (SourceEqualityOpenOrdinaryHead.node [openEdge.1] openEdge.2
    (SourceEqualityRequiredSemanticCache.edge 1 false _ leafNode.2 leaf_semantic open_inputs)
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ open_edge.2.1)).2.1
private theorem source_available : Available heap value :=
  (SourceEqualityOpenOrdinaryHead.node [openEdge.1] openEdge.2
    (SourceEqualityRequiredSemanticCache.edge 1 false _ leafNode.2 leaf_semantic open_inputs)
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ open_edge.2.1)).2.2.1
private theorem source_costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  have first : InternedFreshOrdinaryCostHeap.Heap leafNode.2 :=
    InternedFreshOrdinaryCostHeap.preserve leafEdge.2 leafNode.2 InternedFreshOrdinaryCostHeap.empty_heap
      (InternedShallowHeap.makeNode_noNewMu [leafEdge.1] leafEdge.2)
  exact InternedFreshOrdinaryCostHeap.preserve openEdge.2 heap first
    (InternedShallowHeap.makeNode_noNewMu [openEdge.1] openEdge.2)
private theorem leaf_shape : leafNode.1 = .node ⟨0, .node [0]⟩ [leafEdge.1] 0 [] := by cbv
private theorem source_shape : value = .node ⟨1, .node [1]⟩ [openEdge.1] 0 [.depth] := by cbv
private theorem source_open : value.free ≠ [] := by rw [source_shape]; decide
private theorem source_support : NodeSupport (fun _ => false) heap needed value := by
  intro path tip nonroot
  cases tip with
  | @child index entries child path found rest =>
      have member := SourceEqualityNeededMap.lookup_mem (Int.ofNat index) _ _ found
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      have zero : index = 0 := Int.ofNat.inj member.1
      subst index
      refine Or.inr ⟨source_available, ?_⟩
      rw [source_shape]
      apply SourceCurrentSecondaryTrace.NodeTrace.branches (by decide)
      have first : SourceCurrentSecondaryTrace.NodeTrace (fun _ => false) path leafNode.1 heap false heap := by
        rw [leaf_shape]
        exact .finite rfl
      exact .next (.present (by rw [open_edge.2.2]; rfl) first) .nil


private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩
private theorem fits : SourceCurrentConstrainedCapRequiredResources.HeapFits profile heap :=
  ⟨Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap source_semantic.ready.semantic.1.normal.facts⟩
private theorem valid : SourceEqualityNeeded.Valid needed := by
  simp only [needed, SourceEqualityNeeded.Valid, SourceEqualityNeededMap.Ascending]
  simp
private theorem nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed := by
  simp only [needed, SourceEqualityNeededNonnegative.Nonnegative, List.mem_cons, List.not_mem_nil, or_false]
  intro index child member
  cases member
  simp only [Int.le_refl, and_true]
  intro index child impossible
  cases impossible

/-- An open selected ordinary source derives its exact numeric worker and final profile from its initial trie. -/
theorem constructed_open_node :
    ∃ (original : Value Nat Bool) (before : State Nat Bool) (result : Value Nat Bool) (after : State Nat Bool)
      (profile : SourceCurrentAllocatedNativeResourceForecast.Profile),
      original.free ≠ [] ∧ NodeSupport (fun _ => false) before needed original ∧
      RequireNode needed original before result after ∧
      SourceCurrentConstrainedCapRequiredResources.HeapFits
        (SourceCurrentConstrainedCapRequiredForecast.planProfile (sizeOf needed) profile) after ∧
      SourceEqualityRequiredWorker.require (SourceCurrentRequiredWorkerNumeric.workFuel needed)
        (SourceCurrentConstrainedCapRequiredResources.readFuel
          (SourceCurrentConstrainedCapRequiredForecast.planProfile (sizeOf needed) profile)) needed original before =
        .done result after := by
  let children : RequireChildren [(0, .node [])] 0 [leafNode.1, .reference .depth] heap
      [leafNode.1, .reference .depth] heap :=
    .selected 0 rfl .identity (.unselected 1 rfl .nil)
  let edge := run (makeEdge openEdge.1.entry.key.symbol openEdge.1.entry.key.constraint
    [leafNode.1, .reference .depth]) heap
  let result := run (makeNode [edge.1]) edge.2
  have rows : RequireRows [(0, .node [])] [openEdge.1] heap [edge.1] edge.2 := by
    refine .kept (by rw [open_edge.2.2]; decide) ?_ rfl .nil
    simpa only [open_edge.2.2] using children
  have actual : RequireNode needed value heap result.1 result.2 := by
    rw [source_shape]
    exact .ordinary (by decide) rows rfl
  have returned := SourceCurrentConstrainedCapRequiredNumeric.at_size (fun _ => false) heap source_semantic
    needed valid nonnegative actual source_semantic source_costs source_available (grows_refl _) source_support profile fits
  exact ⟨value, heap, result.1, result.2, profile, source_open, source_support, actual, returned.1,
    SourceCurrentRequiredNumericReplay.node_replay returned.2 _ _ (Nat.le_refl _) (Nat.le_refl _)⟩
end MicroCFTA.RequiredNodeKernels

#print axioms MicroCFTA.RequiredNodeKernels.constructed_open_node
#check @MicroCFTA.RequiredNodeKernels.constructed_open_node
#print MicroCFTA.RequiredNodeKernels.constructed_open_node
