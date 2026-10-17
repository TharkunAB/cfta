import MicroCFTA.SourceCurrentMemoMergeResourceControl
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.MergeResourceControlIntegration
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeResourceControl
open SourceCurrentMemoMergeGraph (Code Run Call Memo remember winner)
open SourceMergedComparisonNumeric (comparisonFuel)

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .node [.mk 1 true []],
    .union [.binder true (.node [.mk 0 true [.var 0], .mk 1 true []]), .node [.mk 2 true []]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive : Value Nat Bool := (children root).getD 0 .empty
private def narrow : Value Nat Bool := (children root).getD 1 .empty
private def alternatives : Value Nat Bool := (children root).getD 2 .empty
private def inputs := [recursive, narrow, alternatives]
private def mass := InternedValueMassHeap.initialBound heap
private def base := initialBound heap.nodes.next heap.edges.next mass
private def edgeResult := run (makeEdge 42 false inputs) heap
private def edgeBound := primitiveGrowth inputs.length base
private def nodeResult := run (makeNode [edgeResult.1]) edgeResult.2
private def workHeap := nodeResult.2
private def workBound := primitiveGrowth 1 edgeBound
private def selected := SourceMergedSelection.select id 4 inputs workHeap
private def after := selected.state
private def fuel := comparisonFuel workBound workBound workBound
private def finalBound := selectionGrowth workBound
private def program : Code Nat Bool (List (Value Nat Bool)) :=
  .bind (.work (makeEdge 42 false inputs)) fun edge =>
    .bind (.work (makeNode [edge])) fun _ => .select inputs

private theorem constructed : built = .done root heap := by cbv
private theorem child_list : children root = inputs := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
private theorem available : Values heap inputs := by
  have parent := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  intro value member
  exact parent.children value (by simpa only [child_list] using member)
private theorem closed : ClosedValues inputs := by
  intro value member
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cbv
private theorem initial_fits : Fits base heap := initial heap mass
  (InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts)
private theorem edge_physical :
    SourceEqualityRequiredCache.Keeps heap edgeResult.2 ∧
      EdgeResident edgeResult.2 edgeResult.1 ∧ edgeResult.1.children = inputs :=
  SourceEqualityRequiredCache.edge 42 false inputs heap semantic.ready available
private theorem edge_semantic : SourceEqualityRequiredSemanticCache.SemanticReady edgeResult.2 :=
  SourceEqualityRequiredSemanticCache.edge 42 false inputs heap semantic available
private theorem rows_resident : Edges edgeResult.2 [edgeResult.1] := by
  intro row member
  obtain rfl := List.mem_singleton.mp member
  exact edge_physical.2.1
private theorem rows_closed : ClosedEdges [edgeResult.1] := by
  intro row member
  obtain rfl := List.mem_singleton.mp member
  rw [edge_physical.2.2]
  exact closed
private theorem work_keeps : SourceEqualityRequiredCache.Keeps heap workHeap :=
  edge_physical.1.trans (SourceEqualityRequiredCache.node [edgeResult.1] edgeResult.2
    edge_semantic.ready rows_resident rows_closed).1
private theorem work_semantic : SourceEqualityRequiredSemanticCache.SemanticReady workHeap :=
  SourceEqualityRequiredSemanticCache.node [edgeResult.1] edgeResult.2 edge_semantic rows_resident rows_closed
private theorem work_available : Values workHeap inputs :=
  fun value member => work_keeps.available value (available value member)
private theorem edge_fits : Fits edgeBound edgeResult.2 :=
  (SourceCurrentMemoMergeResourceControl.edge 42 false inputs heap base inputs.length initial_fits available (Nat.le_refl _)).1
private theorem work_fits : Fits workBound workHeap :=
  (SourceCurrentMemoMergeResourceControl.node [edgeResult.1] edgeResult.2 edgeBound 1 edge_fits rows_resident (Nat.le_refl _)).1
private theorem literal : SourceMergedSelection.select id 4 inputs workHeap = .done [recursive, alternatives] after := by cbv

private theorem computed :
    SourceMergedSelection.select id fuel inputs workHeap = .done [recursive, alternatives] after ∧
      SourceMergedComparisonEffects.Effect workHeap after ∧ Fits finalBound after ∧
      ∀ extra, SourceMergedSelection.select id (fuel + extra) inputs workHeap = .done [recursive, alternatives] after := by
  obtain ⟨result, final, done, effects, fits, stable⟩ :=
    selection_complete id inputs workHeap workBound work_semantic work_fits work_available closed
  have exactReturn := selection_replay id 4 inputs workHeap workBound work_semantic work_fits work_available closed
    [recursive, alternatives] after literal
  obtain ⟨rfl, rfl⟩ := MergedSourceComparison.Result.done.inj (done.symm.trans exactReturn.2.2.1)
  exact ⟨done, effects, fits, stable⟩

/-- Literal edge and node Work precede an allocating Mu/union selection at own initial scalar fuel. -/
theorem work_then_selection :
    built = .done root heap ∧ Fits base heap ∧ Fits edgeBound edgeResult.2 ∧ Fits workBound workHeap ∧
      (match recursive with | .mu .. => True | _ => False) ∧
      (match alternatives with | .union .. => True | _ => False) ∧
      workHeap.nodes.next < after.nodes.next ∧ workHeap.edges.next < after.edges.next ∧
      Run id true program heap SourceCurrentMemoMergeGraph.empty [recursive, alternatives] after SourceCurrentMemoMergeGraph.empty ∧
      Fits finalBound after ∧
      ∀ extra, SourceMergedSelection.select id (fuel + extra) inputs workHeap = .done [recursive, alternatives] after := by
  have actual : Run id true program heap SourceCurrentMemoMergeGraph.empty [recursive, alternatives] after SourceCurrentMemoMergeGraph.empty :=
    .bind (.work _ _ _) (.bind (.work _ _ _) (.select fuel computed.1))
  exact ⟨constructed, initial_fits, edge_fits, work_fits, by cbv, by cbv, by cbv, by cbv,
    actual, computed.2.2.1, computed.2.2.2⟩

private def memo : Memo Nat Bool := remember SourceCurrentMemoMergeGraph.empty recursive recursive
private theorem memo_found : memo recursive.referenceOf = some ⟨recursive, recursive⟩ :=
  (SourceCurrentMemoMergeGraph.remember_absent _ _ _ rfl).1
private theorem recursive_available : Available after recursive :=
  computed.2.1.1.available recursive (work_available recursive (by simp [inputs]))
private theorem memo_physical : SourceCurrentMemoMergeEffects.Stored after memo :=
  SourceCurrentMemoMergeEffects.stored_remember (SourceCurrentMemoMergeEffects.stored_empty after) recursive recursive
    recursive_available recursive_available (fun closed => closed)

/-- An actual published Mu entry remains the warm winner even when the new candidate is smaller. -/
theorem published_warm_winner :
    Call id true recursive after SourceCurrentMemoMergeGraph.empty recursive after memo ∧
      Call id true recursive after memo recursive after memo ∧
      winner memo recursive .empty = ⟨recursive, recursive⟩ ∧
      InternedValueMass.value (.empty : Value Nat Bool) < InternedValueMass.value recursive ∧
      Available after (winner memo recursive .empty).result ∧
      InternedValueMass.value (winner memo recursive .empty).result ≤ finalBound ∧ Fits finalBound after := by
  have body : SourceCurrentMemoMergeGraph.body true recursive = .pure recursive := by cbv
  have raw : Call id true recursive after SourceCurrentMemoMergeGraph.empty
      (winner SourceCurrentMemoMergeGraph.empty recursive recursive).result after memo :=
    .miss rfl (by rw [body]; exact .pure _ _ _)
  have first : Call id true recursive after SourceCurrentMemoMergeGraph.empty recursive after memo := by
    simpa only [(SourceCurrentMemoMergeGraph.remember_absent SourceCurrentMemoMergeGraph.empty recursive recursive rfl).2] using raw
  have warm : Call id true recursive after memo recursive after memo := .hit memo_found
  have retained := (SourceCurrentMemoMergeGraph.winner_existing memo recursive .empty ⟨recursive, recursive⟩ memo_found).2
  have bounded := winner_bound memo_physical computed.2.2.1 recursive .empty (empty_available after)
  exact ⟨first, warm, retained, by cbv, bounded.1, bounded.2, computed.2.2.1⟩

end MicroCFTA.MergeResourceControlIntegration

#print axioms MicroCFTA.MergeResourceControlIntegration.work_then_selection
#check @MicroCFTA.MergeResourceControlIntegration.work_then_selection
#print axioms MicroCFTA.MergeResourceControlIntegration.published_warm_winner
#check @MicroCFTA.MergeResourceControlIntegration.published_warm_winner
