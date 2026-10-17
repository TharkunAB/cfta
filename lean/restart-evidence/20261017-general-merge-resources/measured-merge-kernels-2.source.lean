import MicroCFTA.SourceCurrentMemoMergeMeasured
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MeasuredMergeIntegration
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeMeasured
open SourceCurrentMemoMergeGraph (Code Memo)

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 0 true [.node [.mk 1 true []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def base : Value Nat Bool := (children root).getD 0 .empty
private def rootRow : EdgeValue Nat Bool := (InternedEdgeResidency.nodeEdges root)[0]'(by cbv)
private def baseRow : EdgeValue Nat Bool := (InternedEdgeResidency.nodeEdges base)[0]'(by cbv)
private def initial : Memo Nat Bool := SourceCurrentMemoMergeGraph.empty
private def middle : Memo Nat Bool := SourceCurrentMemoMergeGraph.remember initial base base
private def saved : Memo Nat Bool := SourceCurrentMemoMergeGraph.remember middle root root

private theorem constructed : built = .done root heap := by cbv
private theorem baseRows : InternedEdgeResidency.nodeEdges base = [baseRow] := by cbv
private theorem rootRows : InternedEdgeResidency.nodeEdges root = [rootRow] := by cbv
private theorem baseChildren : baseRow.children = [] := by cbv
private theorem rootChildren : rootRow.children = [base] := by cbv
private theorem baseEdge : run (makeEdge baseRow.entry.key.symbol baseRow.entry.key.constraint []) heap = (baseRow, heap) := by cbv
private theorem rootEdge : run (makeEdge rootRow.entry.key.symbol rootRow.entry.key.constraint [base]) heap = (rootRow, heap) := by cbv
private theorem baseNode : run (makeNode [baseRow]) heap = (base, heap) := by cbv
private theorem rootNode : run (makeNode [rootRow]) heap = (root, heap) := by cbv
private theorem baseBody : SourceCurrentMemoMergeGraph.body true base = SourceCurrentMemoMergeGraph.root true [[baseRow]] := by cbv
private theorem rootBody : SourceCurrentMemoMergeGraph.body true root = SourceCurrentMemoMergeGraph.root true [[rootRow]] := by cbv
private theorem baseWinner : SourceCurrentMemoMergeGraph.winner initial base base = ⟨base, base⟩ := by cbv
private theorem rootAbsent : middle root.referenceOf = none := by cbv
private theorem rootWinner : SourceCurrentMemoMergeGraph.winner middle root root = ⟨root, root⟩ := by cbv

private theorem singleton_map {Input Output : Type} {call : Input → Code Nat Bool Output}
    {input : Input} {value : Output} {cost : Nat} {before after : State Nat Bool}
    {memo current : Memo Nat Bool}
    (first : MeasuredRun (fun guard => guard) true cost (call input) before memo value after current) :
    MeasuredRun (fun guard => guard) true (cost + 4) (SourceCurrentMemoMergeGraph.map call [input]) before memo [value] after current :=
  .bind first (.bind (.pure [] after current) (.pure [value] after current))

private theorem singleton_ready {Input Output : Type} {call : Input → Code Nat Bool Output}
    {input : Input} {value : Output} {cost : Nat} {before after : State Nat Bool}
    {memo current : Memo Nat Bool}
    {first : MeasuredRun (fun guard => guard) true cost (call input) before memo value after current}
    (ready : SelectionReady 0 first) : SelectionReady 0 (singleton_map first) :=
  .bind ready (.bind (.pure [] after current) (.pure [value] after current))

private theorem baseSmall : MeasuredRun (fun guard => guard) true 3 (SourceCurrentMemoMergeGraph.small baseRow) heap initial baseRow heap initial := by
  rw [SourceCurrentMemoMergeGraph.small, baseChildren]
  have actual : MeasuredRun (fun guard => guard) true 1 (.work (makeEdge baseRow.entry.key.symbol baseRow.entry.key.constraint []))
      heap initial baseRow heap initial := by simpa only [baseEdge] using MeasuredRun.work (clear := fun guard => guard) (top := true) _ heap initial
  exact .bind (.pure [] heap initial) actual
private theorem baseSmallReady : SelectionReady 0 baseSmall := by
  unfold SourceCurrentMemoMergeGraph.small
  simp only [baseChildren]
  exact .bind (.pure [] heap initial) (.work _ heap initial)

private theorem baseGroup : MeasuredRun (fun guard => guard) true 7 (SourceCurrentMemoMergeGraph.group true [baseRow]) heap initial [baseRow] heap initial := by
  rw [SourceCurrentMemoMergeGraph.group_small true [baseRow] (by decide)]
  exact singleton_map baseSmall
private theorem baseGroupReady : SelectionReady 0 baseGroup := by
  rw [SourceCurrentMemoMergeGraph.group_small true [baseRow] (by decide)]
  exact singleton_ready baseSmallReady

private theorem baseMeasured : MeasuredCall (fun guard => guard) true 14 base heap initial base heap middle := by
  have body : MeasuredRun (fun guard => guard) true 13 (SourceCurrentMemoMergeGraph.body true base) heap initial base heap initial := by
    rw [baseBody, SourceCurrentMemoMergeGraph.root]
    have node : MeasuredRun (fun guard => guard) true 1 (.work (makeNode [baseRow])) heap initial base heap initial := by
      simpa only [baseNode] using MeasuredRun.work (clear := fun guard => guard) (top := true) _ heap initial
    exact .bind (singleton_map baseGroup) node
  have actual := MeasuredCall.miss (clear := fun guard => guard) (top := true) (input := base) rfl body
  simpa only [baseWinner] using actual
private theorem baseReady : CallSelectionReady 0 baseMeasured := by
  apply CallSelectionReady.miss rfl
  rw [baseBody, SourceCurrentMemoMergeGraph.root]
  exact .bind (singleton_ready baseGroupReady) (.work _ heap initial)

private theorem rootSmall : MeasuredRun (fun guard => guard) true 21 (SourceCurrentMemoMergeGraph.small rootRow) heap initial rootRow heap middle := by
  rw [SourceCurrentMemoMergeGraph.small, rootChildren]
  have edge : MeasuredRun (fun guard => guard) true 1 (.work (makeEdge rootRow.entry.key.symbol rootRow.entry.key.constraint [base])) heap middle rootRow heap middle := by
    simpa only [rootEdge] using MeasuredRun.work (clear := fun guard => guard) (top := true) _ heap middle
  exact .bind (singleton_map (.request baseMeasured)) edge
private theorem rootSmallReady : SelectionReady 0 rootSmall := by
  unfold SourceCurrentMemoMergeGraph.small
  simp only [rootChildren]
  exact .bind (singleton_ready (.request baseReady)) (.work _ heap middle)

private theorem rootGroup : MeasuredRun (fun guard => guard) true 25 (SourceCurrentMemoMergeGraph.group true [rootRow]) heap initial [rootRow] heap middle := by
  rw [SourceCurrentMemoMergeGraph.group_small true [rootRow] (by decide)]
  exact singleton_map rootSmall
private theorem rootGroupReady : SelectionReady 0 rootGroup := by
  rw [SourceCurrentMemoMergeGraph.group_small true [rootRow] (by decide)]
  exact singleton_ready rootSmallReady

private theorem rootMeasured : MeasuredCall (fun guard => guard) true 32 root heap initial root heap saved := by
  have body : MeasuredRun (fun guard => guard) true 31 (SourceCurrentMemoMergeGraph.body true root) heap initial root heap middle := by
    rw [rootBody, SourceCurrentMemoMergeGraph.root]
    have node : MeasuredRun (fun guard => guard) true 1 (.work (makeNode [rootRow])) heap middle root heap middle := by
      simpa only [rootNode] using MeasuredRun.work (clear := fun guard => guard) (top := true) _ heap middle
    exact .bind (singleton_map rootGroup) node
  simpa only [rootWinner] using MeasuredCall.miss (clear := fun guard => guard) (top := true) rootAbsent body
private theorem rootReady : CallSelectionReady 0 rootMeasured := by
  apply CallSelectionReady.miss rootAbsent
  rw [rootBody, SourceCurrentMemoMergeGraph.root]
  exact .bind (singleton_ready rootGroupReady) (.work _ heap middle)

private def code : Code Nat Bool (Value Nat Bool) :=
  .bind (.request root) fun value => .bind (.select [value]) fun _ => .pure value
private theorem selected : SourceMergedSelection.select (fun guard => guard) 0 [root] heap = .done [root] heap := by cbv
private theorem measured : MeasuredRun (fun guard => guard) true 37 code heap initial root heap saved :=
  .bind (.request rootMeasured) (.bind (.select 0 selected) (.pure root heap saved))
private theorem ready : SelectionReady 0 measured :=
  .bind (.request rootReady) (.bind (.select 0 selected selected) (.pure root heap saved))

/-- Actual nested misses, constructors, and selection replay at both larger fuel indices. -/
theorem nested_misses (workExtra selectionExtra : Nat) :
    built = .done root heap ∧
    MeasuredRun (fun guard => guard) true 37 code heap initial root heap saved ∧
    SourceCurrentMemoMergeWorker.execute (fun guard => guard) true (37 + workExtra) selectionExtra code heap initial =
      .done root heap saved ∧
    saved base.referenceOf = some ⟨base, base⟩ ∧ saved root.referenceOf = some ⟨root, root⟩ := by
  exact ⟨constructed, measured, run_replay measured 0 ready _ _ (by omega) (Nat.zero_le _), by cbv, by cbv⟩

/-- A following call reads the actual produced winner without changing heap or memo. -/
theorem warm_hit (workExtra selectionFuel : Nat) :
    SourceCurrentMemoMergeWorker.call (fun guard => guard) true 32 0 root heap initial = .done root heap saved ∧
    SourceCurrentMemoMergeWorker.call (fun guard => guard) true (1 + workExtra) selectionFuel root heap saved =
      .done root heap saved := by
  have found : saved root.referenceOf = some ⟨root, root⟩ := by cbv
  have actual : MeasuredCall (fun guard => guard) true 1 root heap saved root heap saved := .hit found
  exact ⟨call_replay rootMeasured 0 rootReady _ _ (Nat.le_refl _) (Nat.le_refl _),
    call_replay actual 0 (.hit found) _ _ (by omega) (Nat.zero_le _)⟩

/-- A later distinct candidate cannot replace the exact winner published by the nested actual call. -/
theorem current_winner :
    SourceCurrentMemoMergeWorker.call (fun guard => guard) true 32 0 root heap initial = .done root heap saved ∧
    root ≠ Value.empty ∧ SourceCurrentMemoMergeGraph.winner saved root Value.empty = ⟨root, root⟩ ∧ SourceCurrentMemoMergeGraph.remember saved root Value.empty = saved := by
  have found : saved root.referenceOf = some ⟨root, root⟩ := by cbv
  have kept := SourceCurrentMemoMergeGraph.winner_existing saved root Value.empty ⟨root, root⟩ found
  exact ⟨call_replay rootMeasured 0 rootReady _ _ (Nat.le_refl _) (Nat.le_refl _), by cbv, kept.2, kept.1⟩

end MicroCFTA.MeasuredMergeIntegration

#print axioms MicroCFTA.MeasuredMergeIntegration.nested_misses
#check @MicroCFTA.MeasuredMergeIntegration.nested_misses
#print axioms MicroCFTA.MeasuredMergeIntegration.warm_hit
#check @MicroCFTA.MeasuredMergeIntegration.warm_hit
#print axioms MicroCFTA.MeasuredMergeIntegration.current_winner
#check @MicroCFTA.MeasuredMergeIntegration.current_winner
