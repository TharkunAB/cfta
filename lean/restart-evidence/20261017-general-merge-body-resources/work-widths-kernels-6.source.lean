import MicroCFTA.SourceCurrentMemoMergeWorkWidths
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryCosts

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.MergeWorkWidthsIntegration
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect Contract EdgeReady ValueReady)
open SourceCurrentMemoMergeResourceCertificate (Checked)
open SourceCurrentMemoMergeWorkWidths
open SourceCurrentMemoMergeResourceControl (Fits primitiveGrowth)

private def loop : InternedNestedConstruction.Syntax Nat Nat :=
  .binder false (.node [.mk 1 0 [.var 0]])
private def expression : InternedNestedConstruction.Syntax Nat Nat :=
  .node [.mk 77 0 [loop], .mk 77 1 [loop], .mk 77 2 [loop], .mk 77 3 [loop], .mk 77 4 [loop]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Nat Nat := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def rows := nodeEdges original
private def recursive := (children original).getD 0 .empty
private def columnInputs := [recursive, recursive, recursive, recursive, recursive]
private def clear : Nat → Bool := fun _ => true
private def edgeResult := run (makeEdge 77 999 [recursive]) heap
private def nodeResult := run (makeNode [edgeResult.1]) edgeResult.2
private def bound := InternedValueMass.value original
private def width := (bound + 1)^2
private def mass := InternedValueMassHeap.initialBound heap
private def start := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next mass

private theorem constructed : built = .done original heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression original heap constructed
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  exact InternedFreshOrdinaryCosts.closed_heap expression
private theorem original_available : Available heap original :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result original heap constructed
private theorem initial_fits : Fits start heap := SourceCurrentMemoMergeResourceControl.initial heap mass
  (InternedValueMassHeap.initial heap semantic.ready.semantic.1.normal.facts)
private theorem shape : rows.length = 5 ∧ MergedSourceGrouping.groups rows = [rows] ∧
    (match recursive with | .mu .. => True | _ => False) ∧
    MergedAlternativesGroups.columns (rows.map EdgeValue.children) 1 = [columnInputs] := by cbv
private theorem recursive_available : Available heap recursive := by
  exact original_available.children recursive (by cbv; exact List.mem_cons_self)
private theorem recursive_closed : recursive.free = [] := by cbv
private theorem selected : SourceMergedSelection.select clear 2 columnInputs heap = .done [recursive] heap := by cbv
private theorem column_run : Run clear 999 (column columnInputs) heap SourceCurrentMemoMergeGraph.empty
    recursive heap SourceCurrentMemoMergeGraph.empty :=
  .bind (.select 2 selected) (.pure _ _ _)
private theorem columns_run : Run clear 999 (SourceCurrentMemoMergeGraph.map column [columnInputs]) heap SourceCurrentMemoMergeGraph.empty
    [recursive] heap SourceCurrentMemoMergeGraph.empty :=
  .bind column_run (.bind (.pure _ _ _) (.pure _ _ _))
private theorem large_run : Run clear 999 (large 999 (rows.headD (run (makeEdge 0 0 []) heap).1) rows.tail) heap SourceCurrentMemoMergeGraph.empty
    edgeResult.1 edgeResult.2 SourceCurrentMemoMergeGraph.empty := by
  have code : large 999 (rows.headD (run (makeEdge 0 0 []) heap).1) rows.tail =
      .bind (SourceCurrentMemoMergeGraph.map column [columnInputs]) (fun values => .work (makeEdge 77 999 values)) := by cbv
  rw [code]
  exact .bind columns_run (.work _ _ _)

/-- Five original guard-distinct rows take the large branch over a productive Mu column. -/
theorem five_row_body :
    rows.length = 5 ∧ MergedSourceGrouping.groups rows = [rows] ∧
      (match recursive with | .mu .. => True | _ => False) ∧
      Checked width clear (body 999 original) heap (fun after output => Contract original heap output after) ∧
      Run clear 999 (body 999 original) heap SourceCurrentMemoMergeGraph.empty
        nodeResult.1 nodeResult.2 SourceCurrentMemoMergeGraph.empty ∧
      Available nodeResult.2 nodeResult.1 ∧ nodeResult.1.free = [] ∧
      (∀ current, Fits current edgeResult.2 → Fits (primitiveGrowth width current) nodeResult.2) := by
  have checked := body_checked clear 999 original heap semantic costs original_available bound (Nat.le_refl _)
  have groupRun : Run clear 999 (group 999 rows) heap SourceCurrentMemoMergeGraph.empty
      [edgeResult.1] edgeResult.2 SourceCurrentMemoMergeGraph.empty := by
    have code : group 999 rows = .bind (large 999 (rows.headD (run (makeEdge 0 0 []) heap).1) rows.tail)
        (fun edge => .pure [edge]) := by cbv
    rw [code]
    exact .bind large_run (.pure _ _ _)
  have groupsRun : Run clear 999 (SourceCurrentMemoMergeGraph.map (group 999) [rows]) heap SourceCurrentMemoMergeGraph.empty
      [[edgeResult.1]] edgeResult.2 SourceCurrentMemoMergeGraph.empty :=
    .bind groupRun (.bind (.pure _ _ _) (.pure _ _ _))
  have actual : Run clear 999 (body 999 original) heap SourceCurrentMemoMergeGraph.empty
      nodeResult.1 nodeResult.2 SourceCurrentMemoMergeGraph.empty := by
    have code : body 999 original = .bind (SourceCurrentMemoMergeGraph.map (group 999) [rows])
        (fun rows => .work (makeNode rows.flatten)) := by cbv
    rw [code]
    exact .bind groupsRun (.work _ _ _)
  have returned := SourceCurrentMemoMergeEffects.run_effects actual _ semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty heap) checked.erase
  have rootChecked := checked
  have code : body 999 original = .bind (SourceCurrentMemoMergeGraph.map (group 999) [rows])
      (fun rows => .work (makeNode rows.flatten)) := by cbv
  rw [code] at rootChecked
  obtain ⟨intermediate, firstChecked, later⟩ := rootChecked
  have middle := SourceCurrentMemoMergeEffects.run_effects groupsRun intermediate semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty heap) firstChecked.erase
  have final := later _ _ middle.1 middle.2.2
  exact ⟨shape.1, shape.2.1, shape.2.2.1, checked, actual,
    returned.2.2.1, returned.2.2.2 (by cbv), final.2.1⟩

/-- A recursive-boundary union derives its actual warm winner and complete current-heap bound. -/
theorem retained_recursive_union :
    Checked 2 clear (retainedColumn [recursive, recursive]) heap ValueReady ∧
      (∀ current, Fits current heap →
        Fits (primitiveGrowth 2 current) (run (makeUnion [recursive, recursive]) heap).2) ∧
      Run clear 999 (retainedColumn [recursive, recursive]) heap SourceCurrentMemoMergeGraph.empty
        (run (makeUnion [recursive, recursive]) heap).1 (run (makeUnion [recursive, recursive]) heap).2
        SourceCurrentMemoMergeGraph.empty := by
  have available : Values heap [recursive, recursive] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact recursive_available
    · exact List.mem_singleton.mp member ▸ recursive_available
  have closed : ClosedValues [recursive, recursive] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact recursive_closed
    · exact List.mem_singleton.mp member ▸ recursive_closed
  have checked := retained_checked 2 clear [recursive, recursive] heap semantic costs available closed (by simp)
  have code : retainedColumn [recursive, recursive] = .work (makeUnion [recursive, recursive]) := by cbv
  rw [code] at checked
  exact ⟨by rw [code]; exact checked, checked.2.1, by rw [code]; exact .work _ _ _⟩

/-- A warm request may return a larger payload without changing the small row's literal width. -/
theorem small_warm_larger_result :
    InternedValueMass.value recursive < InternedValueMass.value original ∧
      Checked 1 clear (small (rows.headD (run (makeEdge 0 0 []) heap).1)) heap EdgeReady ∧
      Run clear 999 (small (rows.headD (run (makeEdge 0 0 []) heap).1)) heap
        (remember SourceCurrentMemoMergeGraph.empty recursive original)
        (run (makeEdge 77 0 [original]) heap).1 (run (makeEdge 77 0 [original]) heap).2
        (remember SourceCurrentMemoMergeGraph.empty recursive original) ∧
      (∀ current, Fits current heap →
        Fits (primitiveGrowth 1 current) (run (makeEdge 77 0 [original]) heap).2) := by
  let first := rows.headD (run (makeEdge 0 0 []) heap).1
  let memo := remember SourceCurrentMemoMergeGraph.empty recursive original
  have found : memo recursive.referenceOf = some ⟨recursive, original⟩ :=
    (remember_absent SourceCurrentMemoMergeGraph.empty recursive original rfl).1
  have warm : Call clear 999 recursive heap memo original heap memo := .hit found
  have requests : Run clear 999 (SourceCurrentMemoMergeGraph.map Code.request [recursive]) heap memo
      [original] heap memo := .bind (.request warm) (.bind (.pure _ _ _) (.pure _ _ _))
  have code : small first = .bind (SourceCurrentMemoMergeGraph.map Code.request [recursive])
      (fun values => .work (makeEdge 77 0 values)) := by dsimp only [first]; cbv
  have actual : Run clear 999 (small first) heap memo (run (makeEdge 77 0 [original]) heap).1
      (run (makeEdge 77 0 [original]) heap).2 memo := by
    rw [code]
    exact .bind requests (.work _ _ _)
  have resident : EdgeResident heap first :=
    InternedEdgeResidency.resident_edges heap semantic.ready.semantic.1.normal.facts.linked original original_available.resident
      first (by dsimp only [first]; cbv; exact List.mem_cons_self)
  have closed : ClosedValues first.children := by
    intro value member
    have children : first.children = [recursive] := by dsimp only [first]; cbv
    rw [children] at member
    exact List.mem_singleton.mp member ▸ recursive_closed
  have checked := small_checked 1 clear first heap semantic costs ⟨resident, closed⟩ (by dsimp only [first]; cbv)
  have selected := checked
  rw [code] at selected
  obtain ⟨intermediate, head, later⟩ := selected
  have stored := SourceCurrentMemoMergeEffects.stored_remember (SourceCurrentMemoMergeEffects.stored_empty heap)
    recursive original recursive_available original_available (fun _ => by cbv)
  have physical := SourceCurrentMemoMergeEffects.run_effects requests intermediate semantic costs stored head.erase
  have final := later _ _ physical.1 physical.2.2
  exact ⟨by cbv, checked, actual, final.2.1⟩

end MicroCFTA.MergeWorkWidthsIntegration

#print axioms MicroCFTA.MergeWorkWidthsIntegration.five_row_body
#check @MicroCFTA.MergeWorkWidthsIntegration.five_row_body
#print axioms MicroCFTA.MergeWorkWidthsIntegration.retained_recursive_union
#check @MicroCFTA.MergeWorkWidthsIntegration.retained_recursive_union
#print axioms MicroCFTA.MergeWorkWidthsIntegration.small_warm_larger_result
#check @MicroCFTA.MergeWorkWidthsIntegration.small_warm_larger_result
