import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.SourceCurrentRequiredSupport
import MicroCFTA.SourceCurrentRequiredComplete
import MicroCFTA.InternedFreshOrdinaryStoredCosts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.RequiredGuardOriginsKernels
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
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, leaf_edge.2.2, List.not_mem_nil] at member
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

/-- An actual selected open ordinary rebuild retains its exact root guard origins. -/
theorem constructed_open_ordinary :
    value.free ≠ [] ∧
    ∃ result after, RequireNode needed value heap result after ∧
      ∀ edge ∈ InternedEdgeResidency.nodeEdges result,
        ∃ original ∈ InternedEdgeResidency.nodeEdges value,
          SourceCurrentRequiredGuardOrigins.RowOrigin original edge := by
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
  refine ⟨source_open, result.1, result.2, actual, ?_⟩
  have origins := SourceCurrentRequiredGuardOrigins.ordinary
    (by simpa only [source_shape] using actual) source_semantic source_costs
    (by simpa only [source_shape] using source_available)
  simpa only [source_shape, InternedEdgeResidency.nodeEdges] using origins

end MicroCFTA.RequiredGuardOriginsKernels

namespace MicroCFTA.RequiredPlainOriginsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityRequiredGraph SourceEqualityNeeded
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def bad : Guard := ⟨none, .top⟩
private def top : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) bad [
    .binder true (.node [.mk ("leaf", .top) top [], .mk ("pair", .top) top [.var 0, .var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive := (children root)[0]?.getD .empty
private theorem constructed : built = .done root heap := by cbv
private theorem semantic : SemanticReady heap := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem available : Available heap recursive :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children recursive
    (by cbv; exact .head _)
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap :=
  InternedFreshOrdinaryCosts.closed_heap expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap :=
  SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem accepted : SourceMemoGate.unconstrained recursive = true := by cbv
private theorem closed : recursive.free = [] := by cbv
private def needed : Needed := .node [(0, .node [])]
private theorem root_not_plain : ¬SourceMemoGate.unconstrained root = true := by cbv; intro impossible; cases impossible
private theorem recursive_shape : ∃ entry body depth ordinary, recursive = Value.mu entry body depth ordinary := by
  have shape : (match recursive with | .mu .. => True | _ => False) := by cbv
  cases found : recursive with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [found] at shape

/-- A source-built accepted productive Mu unfolds and supplies own Required and Head zero-origin receipts. -/
theorem constructed_plain_exposure :
    ¬SourceMemoGate.unconstrained root = true ∧ SourceMemoGate.unconstrained recursive = true ∧
    (∃ result after, InternedFreshOrdinaryStoredSubstitution.unfold recursive heap = .done result after ∧
      SourceCurrentConstrainedCapGuardHeap.Heap Plain after ∧ Annotated Plain result ∧
      ∀ edge ∈ InternedEdgeResidency.nodeEdges result,
        SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) ∧
    ∃ result after, RequireNode needed recursive heap result after ∧
      SourceCurrentConstrainedCapGuardHeap.Heap Plain after ∧ Annotated Plain result ∧
      (∀ edge ∈ InternedEdgeResidency.nodeEdges result,
        SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) ∧
      ∃ exposed middle, SourceEqualityRequiredHead.Head recursive heap exposed middle ∧
        SourceCurrentConstrainedCapGuardHeap.Heap Plain middle ∧ Annotated Plain exposed ∧
        ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed,
          SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []) := by
  obtain ⟨unfolded, next, done, _kept, _semantic, _available, _language⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete recursive heap semantic available
  have unfoldedOrigins := SourceCurrentRequiredGuardOrigins.accepted_unfold done semantic available guards accepted
  have support : SourceCurrentRequiredSupport.NodeSupport SourceMemoGate.unconstrained heap needed recursive :=
    fun _ _ _ => Or.inl closed
  obtain ⟨result, after, actual, _kept, _semantic, _available⟩ := SourceCurrentRequiredComplete.node_complete
    SourceMemoGate.unconstrained heap semantic needed (by decide) (by decide) recursive heap semantic available
    (grows_refl _) support
  have resultOrigins := SourceCurrentRequiredGuardOrigins.accepted_node actual semantic costs available guards accepted
  have head : ∃ exposed middle, SourceEqualityRequiredHead.Head recursive heap exposed middle := by
    obtain ⟨entry, body, depth, ordinary, shape⟩ := recursive_shape
    have trace := actual
    rw [shape] at trace
    cases trace with
    | recursive nonempty recursive head body => exact ⟨_, _, by simpa only [shape] using head⟩
  obtain ⟨exposed, middle, head⟩ := head
  have headOrigins := SourceCurrentRequiredGuardOrigins.accepted_head head semantic costs available guards accepted
  exact ⟨root_not_plain, accepted, ⟨unfolded, next, done, unfoldedOrigins⟩,
    result, after, actual, resultOrigins.1, resultOrigins.2.1, resultOrigins.2.2, exposed, middle, head, headOrigins⟩

end MicroCFTA.RequiredPlainOriginsKernels

#print axioms MicroCFTA.RequiredGuardOriginsKernels.constructed_open_ordinary
#check @MicroCFTA.RequiredGuardOriginsKernels.constructed_open_ordinary
#print axioms MicroCFTA.RequiredPlainOriginsKernels.constructed_plain_exposure
#check @MicroCFTA.RequiredPlainOriginsKernels.constructed_plain_exposure
