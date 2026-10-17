import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Actual sequential parents of related children

Both parent edges use the same symbol and complete guard. Each edge uses
its original ordered child list. The theorem constructs every edge and
node request in order and derives their physical readback premises.
The resulting parents agree on Empty and all finite open observations.
-/
namespace MicroCFTA.SourceCurrentRelatedParentConstruction
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservationSurvival (Related)
open SourceCurrentOpenObservations (RowMatch)
open Language

/-- Initial related child lists construct both actual parent records and retain their exact full heap effects. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (firstChildren secondChildren : List (Value Symbol Guard)) (before : State Symbol Guard)
    (ready : Ready before) (firstAvailable : Values before firstChildren) (secondAvailable : Values before secondChildren)
    (paired : All₂ Related firstChildren secondChildren) :
    ∃ firstEdge firstEdgeState first firstState secondEdge secondEdgeState second final,
      run (makeEdge symbol guard firstChildren) before = (firstEdge, firstEdgeState) ∧
      run (makeNode [firstEdge]) firstEdgeState = (first, firstState) ∧
      run (makeEdge symbol guard secondChildren) firstState = (secondEdge, secondEdgeState) ∧
      run (makeNode [secondEdge]) secondEdgeState = (second, final) ∧
      Keeps before firstEdgeState ∧ Keeps firstEdgeState firstState ∧
      Keeps firstState secondEdgeState ∧ Keeps secondEdgeState final ∧
      Available final first ∧ Available final second ∧
      firstEdge.entry.key.symbol = symbol ∧ firstEdge.entry.key.constraint = guard ∧ firstEdge.children = firstChildren ∧
      secondEdge.entry.key.symbol = symbol ∧ secondEdge.entry.key.constraint = guard ∧ secondEdge.children = secondChildren ∧
      Related first second := by
  let firstEdge := run (makeEdge symbol guard firstChildren) before
  let first := run (makeNode [firstEdge.1]) firstEdge.2
  let secondEdge := run (makeEdge symbol guard secondChildren) first.2
  let second := run (makeNode [secondEdge.1]) secondEdge.2
  have firstEdgeKept := SourceEqualityRequiredCache.edge symbol guard firstChildren before ready firstAvailable
  have firstNodeKept := SourceEqualityNativeDemandHeapPrimitives.node [firstEdge.1] firstEdge.2 firstEdgeKept.1.ready
    (fun edge member => (List.mem_singleton.mp member) ▸ firstEdgeKept.2.1)
  have firstWhole := firstEdgeKept.1.trans firstNodeKept.1
  have secondInputs : Values first.2 secondChildren :=
    fun value member => firstWhole.available value (secondAvailable value member)
  have secondEdgeKept := SourceEqualityRequiredCache.edge symbol guard secondChildren first.2 firstWhole.ready secondInputs
  have secondNodeKept := SourceEqualityNativeDemandHeapPrimitives.node [secondEdge.1] secondEdge.2 secondEdgeKept.1.ready
    (fun edge member => (List.mem_singleton.mp member) ▸ secondEdgeKept.2.1)
  have lastWhole := secondEdgeKept.1.trans secondNodeKept.1
  have firstFields := MergedPhysicalGroupEdges.makeEdge_fields before ready.semantic.1.normal.facts
    symbol guard firstChildren firstAvailable
  have secondFields := MergedPhysicalGroupEdges.makeEdge_fields first.2 firstWhole.ready.semantic.1.normal.facts
    symbol guard secondChildren secondInputs
  have rows : RowMatch Related firstEdge.1 secondEdge.1 := by
    refine ⟨firstFields.1.trans secondFields.1.symm, firstFields.2.1.trans secondFields.2.1.symm, ?_⟩
    change All₂ Related (run (makeEdge symbol guard firstChildren) before).1.children
      (run (makeEdge symbol guard secondChildren) first.2).1.children
    rw [firstFields.2.2, secondFields.2.2]
    exact paired
  have reverse : RowMatch Related secondEdge.1 firstEdge.1 := by
    refine ⟨rows.1.symm, rows.2.1.symm, ?_⟩
    have children := rows.2.2
    induction children with
    | nil => exact .nil
    | cons pair tail ih =>
        exact .cons ⟨pair.1.symm, fun depth view => (pair.2 depth view).symm⟩ ih
  have related := SourceCurrentOpenObservationSurvival.makeNode [firstEdge.1] [secondEdge.1] firstEdge.2 secondEdge.2
    firstEdgeKept.1.ready.semantic.1.normal.facts secondEdgeKept.1.ready.semantic.1.normal.facts
    (fun edge member => (List.mem_singleton.mp member) ▸ firstEdgeKept.2.1)
    (fun edge member => (List.mem_singleton.mp member) ▸ secondEdgeKept.2.1)
    (fun row member => ⟨secondEdge.1, List.mem_cons_self, (List.mem_singleton.mp member) ▸ rows⟩)
    (fun row member => ⟨firstEdge.1, List.mem_cons_self, (List.mem_singleton.mp member) ▸ reverse⟩)
  exact ⟨firstEdge.1, firstEdge.2, first.1, first.2, secondEdge.1, secondEdge.2, second.1, second.2,
    rfl, rfl, rfl, rfl, firstEdgeKept.1, firstNodeKept.1, secondEdgeKept.1, secondNodeKept.1,
    lastWhole.available first.1 firstNodeKept.2, secondNodeKept.2,
    firstFields.1, firstFields.2.1, firstFields.2.2, secondFields.1, secondFields.2.1, secondFields.2.2, related⟩

end MicroCFTA.SourceCurrentRelatedParentConstruction
