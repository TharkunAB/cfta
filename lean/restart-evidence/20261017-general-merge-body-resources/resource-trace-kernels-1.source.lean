import MicroCFTA.SourceCurrentMemoMergeResourceTrace
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.MergeResourceTraceIntegration
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeResourceControl
open SourceCurrentMemoMergeGraph (Code Memo remember winner)
open SourceCurrentMemoMergeMeasured
open SourceCurrentMemoMergeResourceTrace
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

private theorem base_le_work : base ≤ workBound :=
  Nat.le_trans (primitiveGrowth_ge inputs.length base) (primitiveGrowth_ge 1 edgeBound)
private theorem edge_le_work : edgeBound ≤ workBound := primitiveGrowth_ge 1 edgeBound
private theorem work_le_final : workBound ≤ finalBound := selectionGrowth_ge workBound
private theorem initial_final : Fits finalBound heap := initial_fits.mono (Nat.le_trans base_le_work work_le_final)
private theorem edge_final : Fits finalBound edgeResult.2 := edge_fits.mono (Nat.le_trans edge_le_work work_le_final)
private theorem work_final : Fits finalBound workHeap := work_fits.mono work_le_final
private theorem after_final : Fits finalBound after := computed.2.2.1

private def measured : MeasuredRun id true 5 program heap SourceCurrentMemoMergeGraph.empty
    [recursive, alternatives] after SourceCurrentMemoMergeGraph.empty :=
  .bind (.work _ _ _) (.bind (.work _ _ _) (.select 4 literal))
private theorem resource_trace : Trace finalBound measured :=
  .bind (.work _ _ _ initial_final edge_final)
    (.bind (.work _ _ _ edge_final work_final)
      (.select 4 literal work_semantic work_final work_available closed after_final))

/-- Actual constructor work and allocating selection replay at one scalar comparison fuel. -/
theorem allocating_selection (workExtra selectionExtra : Nat) :
    built = .done root heap ∧ workHeap.nodes.next < after.nodes.next ∧
      workHeap.edges.next < after.edges.next ∧
      SourceCurrentMemoMergeWorker.execute id true (5 + workExtra)
        (comparisonFuel finalBound finalBound finalBound + selectionExtra)
        program heap SourceCurrentMemoMergeGraph.empty =
        .done [recursive, alternatives] after SourceCurrentMemoMergeGraph.empty ∧
      Fits finalBound heap ∧ Fits finalBound after := by
  exact ⟨constructed, by cbv, by cbv,
    run_replay measured _ resource_trace.selection_ready _ _ (by omega) (by omega),
    resource_trace.initial_fits, resource_trace.final_fits⟩

private def memo : Memo Nat Bool := remember SourceCurrentMemoMergeGraph.empty recursive recursive
private theorem memo_found : memo recursive.referenceOf = some ⟨recursive, recursive⟩ :=
  (SourceCurrentMemoMergeGraph.remember_absent _ _ _ rfl).1
private def firstCall : MeasuredCall id true 2 recursive after SourceCurrentMemoMergeGraph.empty recursive after memo :=
  .miss rfl (.pure recursive after SourceCurrentMemoMergeGraph.empty)
private theorem firstTrace : CallTrace finalBound firstCall :=
  .miss rfl (.pure recursive after SourceCurrentMemoMergeGraph.empty after_final)
private def warmCall : MeasuredCall id true 1 recursive after memo recursive after memo := .hit memo_found
private theorem warmTrace : CallTrace finalBound warmCall := .hit memo_found after_final
private def serial : Code Nat Bool (Value Nat Bool) :=
  .bind program fun _ => .bind (.request recursive) fun value =>
    .bind (.request value) fun final => .pure final
private def serialMeasured : MeasuredRun id true 14 serial heap SourceCurrentMemoMergeGraph.empty recursive after memo :=
  .bind measured (.bind (.request firstCall) (.bind (.request warmCall) (.pure recursive after memo)))
private theorem serialTrace : Trace finalBound serialMeasured :=
  .bind resource_trace (.bind (.request firstTrace) (.bind (.request warmTrace) (.pure recursive after memo after_final)))

/-- The same allocating prefix feeds its exact returned heap into a cold publication and warm hit. -/
theorem nested_publication (workExtra selectionExtra : Nat) :
    SourceCurrentMemoMergeWorker.execute id true (14 + workExtra)
      (comparisonFuel finalBound finalBound finalBound + selectionExtra)
      serial heap SourceCurrentMemoMergeGraph.empty = .done recursive after memo ∧
    memo recursive.referenceOf = some ⟨recursive, recursive⟩ ∧
    Fits finalBound heap ∧ Fits finalBound after := by
  exact ⟨run_replay serialMeasured _ serialTrace.selection_ready _ _ (by omega) (by omega),
    memo_found, serialTrace.initial_fits, serialTrace.final_fits⟩

/-- A larger scalar envelope preserves the same cold winner and full warm returned state. -/
theorem larger_warm (increase workExtra selectionExtra : Nat) :
    SourceCurrentMemoMergeWorker.call id true (2 + workExtra)
      (comparisonFuel (finalBound + increase) (finalBound + increase) (finalBound + increase) + selectionExtra)
      recursive after SourceCurrentMemoMergeGraph.empty = .done recursive after memo ∧
    SourceCurrentMemoMergeWorker.call id true (1 + workExtra)
      (comparisonFuel (finalBound + increase) (finalBound + increase) (finalBound + increase) + selectionExtra)
      recursive after memo = .done recursive after memo ∧ Fits (finalBound + increase) after := by
  have cold := firstTrace.mono (Nat.le_add_right finalBound increase)
  have warm := warmTrace.mono (Nat.le_add_right finalBound increase)
  exact ⟨call_replay firstCall _ cold.selection_ready _ _ (by omega) (by omega),
    call_replay warmCall _ warm.selection_ready _ _ (by omega) (by omega), warm.final_fits⟩

end MicroCFTA.MergeResourceTraceIntegration

#print axioms MicroCFTA.MergeResourceTraceIntegration.allocating_selection
#check @MicroCFTA.MergeResourceTraceIntegration.allocating_selection
#print axioms MicroCFTA.MergeResourceTraceIntegration.nested_publication
#check @MicroCFTA.MergeResourceTraceIntegration.nested_publication
#print axioms MicroCFTA.MergeResourceTraceIntegration.larger_warm
#check @MicroCFTA.MergeResourceTraceIntegration.larger_warm
