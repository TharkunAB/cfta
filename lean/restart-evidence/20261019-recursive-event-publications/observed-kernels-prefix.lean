import MicroCFTA.SourceCurrentRecursiveEntryPublication
import MicroCFTA.SourceCurrentRecursiveEntryPublicationSites
import MicroCFTA.SourceCurrentNativeMuIssuedHistory
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityProjectionAPI
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# An actual ordinary prefix publishes a nested Mu

The closed source has two ordinary rows with distinct used Mu children.
The first child projection publishes a captured nested Mu. The selected
second child starts after that publication. Both child calls are actual.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ObservedPublicationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceCurrentProjectionRecursiveEntry (Entry)
open SourceCurrentClassObservationSpines (ProjectionFrame)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "PublicationHistory" => SourceCurrentNativeMuPublication.History
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def muSource (outer inner : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk (outer,.top) plain
    [.binder false (.node [.mk (inner,.top) plain [.var 1,.var 0]])]])
private def expression : Syntax Symbol Guard := .node
  [.mk ("branch0",.top) plain [muSource "outerA" "innerA"],
   .mk ("branch1",.top) plain [muSource "outerB" "innerB"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def builtValue : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def firstMu : Node := (children builtValue)[0]?.getD .empty
private def secondMu : Node := (children builtValue)[1]?.getD .empty
private def fallback : Row := (run (makeEdge ("unused",.top) plain []) heap).1
private def branch0 : Row := (nodeEdges builtValue)[0]?.getD fallback
private def branch1 : Row := (nodeEdges builtValue)[1]?.getD fallback
private def rootEntry := match builtValue with | .node entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def root : Node := .node rootEntry [branch0,branch1] builtValue.depth builtValue.free
private def firstCalled := SourceEqualityProjectionWorker.project 8 8 [0] firstMu heap
private def firstOutput : Node := match firstCalled with | .done value _ => value | _ => .empty
private def firstAfter : Heap := match firstCalled with | .done _ state => state | _ => heap
private def firstHead := SourceEqualityRequiredWorker.head 8 firstMu heap
private def firstExposed : Node := match firstHead with | .done value _ => value | _ => .empty
private def published : Node := (children firstExposed)[0]?.getD .empty
private def publishedEntry := match published with | .mu entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def publishedBody : Node := match published with | .mu _ body _ _ => body | _ => .empty
private def publishedDepth : Node := match published with | .mu _ _ depth _ => depth | _ => .empty
private def publishedOrdinary : Node := match published with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def secondHead := SourceEqualityRequiredWorker.head 8 secondMu firstAfter
private def secondExposed : Node := match secondHead with | .done value _ => value | _ => .empty
private def secondHeadAfter : Heap := match secondHead with | .done _ state => state | _ => firstAfter
private def secondBodyCalled := SourceEqualityProjectionWorker.project 7 8 [0] secondExposed secondHeadAfter
private def secondOutput : Node := match secondBodyCalled with | .done value _ => value | _ => .empty
private def secondAfter : Heap := match secondBodyCalled with | .done _ state => state | _ => secondHeadAfter
private def firstRow : Row := (nodeEdges firstOutput)[0]?.getD fallback
private def row : Row := (nodeEdges secondOutput)[0]?.getD fallback
private def called := SourceEqualityProjectionWorker.project 9 8 [0,0] root heap
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after : Heap := match called with | .done _ state => state | _ => heap
private def terminal := MergedFreshOrdinaryExposure.nodeEdges 8 result after
private def observed : List Row := match terminal with | .done values _ => values | _ => []
private def readAfter : Heap := match terminal with | .done _ state => state | _ => after

private theorem built_done : built = .done root heap := by cbv
private theorem first_done : firstCalled = .done firstOutput firstAfter := by cbv
private theorem second_head_done : secondHead = .done secondExposed secondHeadAfter := by cbv
private theorem second_body_done : secondBodyCalled = .done secondOutput secondAfter := by cbv
private theorem called_done : called = .done result after := by cbv
private theorem terminal_done : terminal = .done observed readAfter := by cbv
private theorem shapes : branch0.children = [firstMu] ∧ branch1.children = [secondMu] ∧
    observed = [firstRow,row] ∧ Recursive firstMu ∧ Recursive secondMu ∧
    (match firstMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match secondMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    published = .mu publishedEntry publishedBody publishedDepth publishedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal publishedDepth publishedOrdinary = true := by cbv
private theorem new_record : heap.nodeRecords publishedEntry.key = none ∧
    firstAfter.nodeRecords publishedEntry.key = some published := by cbv
private theorem changed : heap ≠ firstAfter := by
  intro same
  have records := congrArg (fun state : Heap => state.nodeRecords publishedEntry.key) same
  rw [new_record.1,new_record.2] at records
  cases records
private theorem semantic : SemanticReady heap := SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem first_project : Project [0] firstMu heap firstOutput firstAfter :=
  SourceEqualityProjectionWorkerSound.project_graph 8 8 [0] firstMu heap firstOutput firstAfter first_done
private theorem second_head : SourceEqualityRequiredHead.Head secondMu firstAfter secondExposed secondHeadAfter :=
  SourceEqualityRequiredWorkerSound.head_graph 8 secondMu firstAfter secondExposed secondHeadAfter second_head_done
private theorem second_body : Project [0] secondExposed secondHeadAfter secondOutput secondAfter :=
  SourceEqualityProjectionWorkerSound.project_graph 7 8 [0] secondExposed secondHeadAfter secondOutput secondAfter second_body_done
private theorem second_project : Project [0] secondMu firstAfter secondOutput secondAfter :=
  .recursive shapes.2.2.2.2.1 second_head second_body
private theorem scan : ProjectRows [0] 0 [branch0,branch1] heap [firstOutput,secondOutput] secondAfter :=
  .selected (by cbv) first_project (.selected (by cbv) second_project .nil)
private theorem first_read : Read firstOutput secondAfter [firstRow] secondAfter := .done 8 (by cbv)
private theorem second_read : Read secondOutput secondAfter [row] secondAfter := .done 8 (by cbv)
private theorem reads : ReadAll [firstOutput,secondOutput] secondAfter [firstRow,row] secondAfter :=
  .cons first_read (.cons second_read .nil)
private theorem united : run (makeNode [firstRow,row]) secondAfter = (result,after) := by cbv
private theorem project : Project [0,0] root heap result after :=
  .ordinary (entry := rootEntry) (depth := root.depth) (free := root.free) scan (.node reads united)
private theorem read : Read result after observed readAfter := .done 8 terminal_done

private theorem first_available : Available heap firstMu :=
  available.children firstMu (by cbv; exact .head _)
private theorem second_available : Available heap secondMu :=
  available.children secondMu (by cbv; exact .tail _ (.head _))
private def frame : ProjectionFrame project read 1 row where
  values := [firstOutput,secondOutput]
  middle := secondAfter
  allRows := [firstRow,row]
  unionMiddle := secondAfter
  projects := scan
  reads := reads
  built := united
  exactProject := rfl
  selected := by rw [shapes.2.2.1]; rfl
  canonical := by cbv
  rawIndex := 1
  raw := rfl
  operandIndex := 1
  operand := secondOutput
  operandSelected := rfl
  earlierRows := [firstRow]
  selectedRows := [row]
  laterRows := []
  readStart := secondAfter
  readFinish := secondAfter
  readPrefix := .cons first_read .nil
  operandRead := second_read
  readSuffix := .nil
  parts := rfl
  readIndex := 0
  readSelected := rfl
  sourceIndex := 1
  sourceRow := branch1
  child := secondMu
  start := firstAfter
  finish := secondAfter
  sourceSelected := by cbv
  childSelected := by cbv
  projectPrefix := .selected (by cbv) first_project .nil
  call := second_project
  projectSuffix := .nil
  rest := by
    have effects := SourceEqualityProjectionCosts.project_effects first_project semantic costs first_available
    exact SourceCurrentProjectionReadSpine.project second_project effects.2.1 effects.2.2.1
      (effects.1.available secondMu second_available) second_read 0 row rfl
private theorem located : Entry project read 1 row [0] secondMu :=
  .ordinary frame 0 rfl (by cbv)
    (.head (recursive := shapes.2.2.2.2.1) (head := second_head) (body := second_body) frame.rest)
private noncomputable def initial_history : PublicationHistory empty heap :=
  SourceCurrentNativeMuPublication.closed_history expression
private noncomputable def initial_issued : SourceCurrentNativeMuIssuedHistory.Path empty heap :=
  SourceCurrentNativeMuIssuedHistory.closed_path expression
private theorem supported : ∃ observation : SourceCurrentRecursiveEntryObservation.Observation secondMu row,
    [0,0] = ([0] : List Nat).map Int.ofNat ++ observation.path ∧
    Keeps heap observation.before ∧ Keeps observation.reader after ∧
    Nonempty (PublicationHistory heap observation.before) := by
  have effects := SourceEqualityProjectionCosts.project_effects project semantic costs available
  have readerGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain project semantic costs available guards
  exact SourceCurrentRecursiveEntryPublication.entry located semantic costs available guards effects.2.1 effects.2.2.1
    (pure_keeps after effects.2.1.ready) readerGuards


end MicroCFTA.ObservedPublicationKernels
