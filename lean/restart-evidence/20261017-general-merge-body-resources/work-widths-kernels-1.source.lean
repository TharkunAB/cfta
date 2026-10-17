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
  have actual := InternedFreshOrdinaryCosts.closed_heap expression
  simpa only [constructed] using actual
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
private theorem large_run : Run clear 999 (large 999 (rows.headD (defaultEdge 0 0)) rows.tail) heap SourceCurrentMemoMergeGraph.empty
    edgeResult.1 edgeResult.2 SourceCurrentMemoMergeGraph.empty := by
  change Run clear 999 (.bind (SourceCurrentMemoMergeGraph.map column [columnInputs])
    (fun values => .work (makeEdge 77 999 values))) heap SourceCurrentMemoMergeGraph.empty _ _ _
  exact .bind columns_run (.work _ _ _)
