import MicroCFTA.SourceCurrentRecursivePlainRead
import MicroCFTA.SourceCurrentRecursiveEntryPlainRead
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentGatePlainRegion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# Actual plain recursive root and Head entries

A source-built used Mu supplies two successful projection/read schedules.
The first reads the recursive root. The second follows a recursive Head
and a real selected child. Both retain the exact first recursive Entry.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.RecursivePlainReaderKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityAnnotationLanguage
open SourceCurrentProjectionRecursiveEntry (Entry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def expression : Syntax Symbol Guard := .binder false (.node [.mk ("rec",.top) plain [.var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def mu : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def rootRead := MergedFreshOrdinaryExposure.nodeEdges 8 mu heap
private def rootRows : List Row := match rootRead with | .done value _ => value | _ => []
private def rootReadAfter : Heap := match rootRead with | .done _ state => state | _ => heap
private def fallback : Row := (run (makeEdge ("unused",.top) plain []) heap).1
private def rootRow : Row := rootRows[0]?.getD fallback
private def projected := SourceEqualityProjectionWorker.project 8 8 [0] mu heap
private def output : Node := match projected with | .done value _ => value | _ => .empty
private def after : Heap := match projected with | .done _ state => state | _ => heap
private def terminalRead := MergedFreshOrdinaryExposure.nodeEdges 8 output after
private def rows : List Row := match terminalRead with | .done value _ => value | _ => []
private def readAfter : Heap := match terminalRead with | .done _ state => state | _ => after
private def row : Row := rows[0]?.getD fallback
private theorem built_done : built = .done mu heap := by cbv
private theorem root_read_done : rootRead = .done rootRows rootReadAfter := by cbv
private theorem project_done : projected = .done output after := by cbv
private theorem terminal_done : terminalRead = .done rows readAfter := by cbv
private theorem shapes : Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    SourceMemoGate.unconstrained mu = true ∧ rootRows = [rootRow] ∧ rows = [row] := by cbv
private theorem semantic : SemanticReady heap := SourceEqualityRequiredSemanticCache.constructed expression mu heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : Available heap mu :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result mu heap built_done
private theorem annotated : Annotated Plain mu :=
  SourceCurrentGatePlainRegion.annotations heap mu semantic.ready.semantic.1.normal.facts.coherent available shapes.2.2.1
private theorem root_case :
    (∃ project : Project [] mu heap mu heap, ∃ read : Read mu heap rootRows rootReadAfter,
      Entry project read 0 rootRow [] mu) ∧ Plain rootRow.entry.key.constraint := by
  let project : Project [] mu heap mu heap := .root
  let read : Read mu heap rootRows rootReadAfter := .done 8 root_read_done
  have selected : rootRows[0]? = some rootRow := by rw [shapes.2.2.2.1]; rfl
  let spine : SourceCurrentProjectionReadSpine.Spine project read 0 rootRow := .root read 0 rootRow selected
  let located : Entry project read 0 rootRow [] mu := .root shapes.1 spine
  have retained := SourceEqualityRequiredCache.pure_keeps heap semantic.ready
  have projectedPlain := SourceCurrentRecursivePlainRead.project_read Plain project semantic costs available guards annotated
    read semantic retained guards rootRow (List.mem_of_getElem? selected)
  exact ⟨⟨project,read,located⟩,projectedPlain⟩
private theorem head_case :
    (∃ project : Project [0] mu heap output after, ∃ read : Read output after rows readAfter,
      Entry project read 0 row [] mu) ∧ Plain row.entry.key.constraint := by
  let project : Project [0] mu heap output after :=
    SourceEqualityProjectionWorkerSound.project_graph 8 8 [0] mu heap output after project_done
  let read : Read output after rows readAfter := .done 8 terminal_done
  have selected : rows[0]? = some row := by rw [shapes.2.2.2.2]; rfl
  have spine := SourceCurrentProjectionReadSpine.project project semantic costs available read 0 row selected
  have head_entry {value : Node} {before result finish reader observed readFinish position selectedRow}
      {call : Project [0] value before result finish} {read : Read result reader observed readFinish}
      (recursive : Recursive value) (remaining : SourceCurrentProjectionReadSpine.Spine call read position selectedRow) :
      Entry call read position selectedRow [] value := by
    cases value with
    | empty | reference | node => cases recursive
    | mu | union =>
      cases call with
      | recursive rec head body => exact .head (recursive := rec) (head := head) (body := body) remaining
  have located := head_entry shapes.1 spine
  have effects := SourceEqualityProjectionCosts.project_effects project semantic costs available
  have afterGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain project semantic costs available guards
  have retained := SourceEqualityRequiredCache.pure_keeps after effects.2.1.ready
  have enteredPlain := SourceCurrentRecursiveEntryPlainRead.entry Plain located annotated semantic costs available guards
    effects.2.1 retained afterGuards
  exact ⟨⟨project,read,located⟩,enteredPlain⟩

private theorem checked_witness :
    built = .done mu heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    Available heap mu ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    Annotated Plain mu ∧ SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
    rootRead = .done rootRows rootReadAfter ∧ rootRows = [rootRow] ∧
    SourceEqualityProjectionWorker.project 8 8 [] mu heap = .done mu heap ∧
    (∃ project : Project [] mu heap mu heap, ∃ read : Read mu heap rootRows rootReadAfter,
      Entry project read 0 rootRow [] mu) ∧ Plain rootRow.entry.key.constraint ∧
    projected = .done output after ∧ terminalRead = .done rows readAfter ∧ rows = [row] ∧
    (∃ project : Project [0] mu heap output after, ∃ read : Read output after rows readAfter,
      Entry project read 0 row [] mu) ∧ Plain row.entry.key.constraint := by
  exact ⟨built_done,semantic,available,shapes.1,shapes.2.1,annotated,guards,root_read_done,shapes.2.2.2.1,
    rfl,root_case.1,root_case.2,project_done,terminal_done,shapes.2.2.2.2,head_case.1,head_case.2⟩

/-- Actual recursive root and Head entries return plain selected rows from derived source support. -/
theorem recursive_reads :
    built = .done mu heap ∧ SourceEqualityRequiredSemanticCache.SemanticReady heap ∧
    Available heap mu ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    Annotated Plain mu ∧ SourceCurrentConstrainedCapGuardHeap.Heap Plain heap ∧
    rootRead = .done rootRows rootReadAfter ∧ rootRows = [rootRow] ∧
    SourceEqualityProjectionWorker.project 8 8 [] mu heap = .done mu heap ∧
    (∃ project : Project [] mu heap mu heap, ∃ read : Read mu heap rootRows rootReadAfter,
      Entry project read 0 rootRow [] mu) ∧ Plain rootRow.entry.key.constraint ∧
    projected = .done output after ∧ terminalRead = .done rows readAfter ∧ rows = [row] ∧
    (∃ project : Project [0] mu heap output after, ∃ read : Read output after rows readAfter,
      Entry project read 0 row [] mu) ∧ Plain row.entry.key.constraint := checked_witness
end MicroCFTA.RecursivePlainReaderKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.RecursivePlainReaderKernels.recursive_reads
#print MicroCFTA.RecursivePlainReaderKernels.recursive_reads
#print axioms MicroCFTA.RecursivePlainReaderKernels.recursive_reads
