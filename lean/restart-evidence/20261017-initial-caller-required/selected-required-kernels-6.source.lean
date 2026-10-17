import MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
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

namespace MicroCFTA.SelectedRequiredKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredGraph SourceEqualityNeeded
open SourceCurrentRequiredSupport
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentConstrainedCap (Cap)

private def annotation (guard : Bool) : Prop := guard = true
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
private theorem source_guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
  have first : SourceCurrentConstrainedCapGuardHeap.Heap annotation leafNode.2 :=
    SourceCurrentConstrainedCapGuardHeap.preserve annotation leafEdge.2 leafNode.2
      (SourceCurrentConstrainedCapGuardHeap.empty_heap annotation)
      (InternedShallowHeap.makeNode_noNewMu [leafEdge.1] leafEdge.2)
  exact SourceCurrentConstrainedCapGuardHeap.preserve annotation openEdge.2 heap first
    (InternedShallowHeap.makeNode_noNewMu [openEdge.1] openEdge.2)
private theorem leaf_shape : leafNode.1 = .node ⟨0, .node [0]⟩ [leafEdge.1] 0 [] := by cbv
private theorem source_shape : value = .node ⟨1, .node [1]⟩ [openEdge.1] 0 [.depth] := by cbv
private theorem leaf_annotated : Annotated annotation leafNode.1 := by
  rw [leaf_shape]
  apply Annotated.node
  · intro edge member
    have same : edge = leafEdge.1 := List.mem_singleton.mp member
    subst edge
    rfl
  · intro child member
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, leaf_edge.2.2, List.not_mem_nil] using member
private theorem source_cap : Cap annotation 1 value := by
  rw [source_shape]
  apply Cap.node 0
  intro child member
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, open_edge.2.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .plain 0 leaf_annotated
  · exact .plain 0 (.reference _)
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

/-- A supported open constrained prefix constructs its own Required call and retains its cap. -/
theorem constructed_open_selected :
    ∃ (original : Value Nat Bool) (before : State Nat Bool) (result : Value Nat Bool) (after : State Nat Bool),
      original.free ≠ [] ∧ NodeSupport (fun _ => false) before needed original ∧
      RequireNode needed original before result after ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after ∧ Cap annotation 1 result := by
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
  have returned := SourceCurrentConstrainedCapSelectedRequired.node annotation 1 actual source_semantic
    source_costs source_available source_guards source_cap
  exact ⟨value, heap, result.1, result.2, source_open, source_support, actual, returned⟩

/-- Empty Needed returns an open reference without a Head or a global memo read. -/
theorem constructed_empty_reference
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))] (memos : EndpointMemoGateTrace.Memos) :
    let inputs : List (Value (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula)) := [.reference .depth]
    ∃ reads : SourceCurrentRequiredQueryMemos.RequireAllReads [] inputs inputs empty empty memos memos,
      SourceCurrentConstrainedCapGuardHeap.Heap
        (fun _ : SourceSymbolicIndex.Constraint FullSyntax.Formula => True)
        (empty (Symbol := SourceObservations.Label FullSyntax.Formula)) ∧
      (∀ value ∈ inputs, Cap (fun _ => True) 0 value) ∧ inputs.length = inputs.length ∧
      ¬MergedColdReaderClosedInputs.ClosedValues inputs := by
  dsimp only
  have actual : RequireChildren (Symbol := SourceObservations.Label FullSyntax.Formula)
      (Guard := SourceSymbolicIndex.Constraint FullSyntax.Formula) [] 0 [.reference .depth] empty [.reference .depth] empty :=
    .unselected 0 rfl .nil
  have reads : SourceCurrentRequiredQueryMemos.RequireAllReads [] [.reference .depth] [.reference .depth]
      empty empty memos memos := ⟨actual, .unselected (absent := rfl) .nil⟩
  have semantic : SemanticReady (empty (Symbol := SourceObservations.Label FullSyntax.Formula)
      (Guard := SourceSymbolicIndex.Constraint FullSyntax.Formula)) :=
    SourceEqualityRequiredSemanticCache.constructed .empty .empty empty (by simp only [InternedFreshOrdinaryConstruction.build])
  have available : Values (empty (Symbol := SourceObservations.Label FullSyntax.Formula)
      (Guard := SourceSymbolicIndex.Constraint FullSyntax.Formula)) [.reference .depth] := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ InternedNestedProvenance.depth_available _
  have caps : ∀ value ∈ [Value.reference (Symbol := SourceObservations.Label FullSyntax.Formula)
      (Guard := SourceSymbolicIndex.Constraint FullSyntax.Formula) .depth], Cap (fun _ => True) 0 value := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ Cap.plain 0 (.reference _)
  have returned := SourceCurrentConstrainedCapSelectedRequired.requireAll (fun _ => True) 0 reads semantic
    InternedFreshOrdinaryCostHeap.empty_heap available (SourceCurrentConstrainedCapGuardHeap.empty_heap _) caps
  refine ⟨reads, returned.1, returned.2.1, returned.2.2, ?_⟩
  intro closed
  have impossible := closed (.reference .depth) List.mem_cons_self
  cases impossible
end MicroCFTA.SelectedRequiredKernels

#print axioms MicroCFTA.SelectedRequiredKernels.constructed_open_selected
#check @MicroCFTA.SelectedRequiredKernels.constructed_open_selected
#print MicroCFTA.SelectedRequiredKernels.constructed_open_selected
#print axioms MicroCFTA.SelectedRequiredKernels.constructed_empty_reference
#check @MicroCFTA.SelectedRequiredKernels.constructed_empty_reference
#print MicroCFTA.SelectedRequiredKernels.constructed_empty_reference
