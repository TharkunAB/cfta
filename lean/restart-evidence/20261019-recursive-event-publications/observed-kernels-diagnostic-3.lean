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
set_option stderrAsMessages false
set_option Elab.async false
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

run_cmd do
  (← IO.getStderr).putStrLn "STAGE built_done"
  (← IO.getStderr).flush
private theorem built_done : built = .done root heap := by cbv
private theorem first_done : firstCalled = .done firstOutput firstAfter := by cbv
private theorem second_head_done : secondHead = .done secondExposed secondHeadAfter := by cbv
private theorem second_body_done : secondBodyCalled = .done secondOutput secondAfter := by cbv
private theorem called_done : called = .done result after := by cbv
private theorem terminal_done : terminal = .done observed readAfter := by cbv
run_cmd do
  (← IO.getStderr).putStrLn "STAGE shapes"
  (← IO.getStderr).flush
private theorem shapes : branch0.children = [firstMu] ∧ branch1.children = [secondMu] ∧
    observed = [firstRow,row] ∧ Recursive firstMu ∧ Recursive secondMu ∧
    (match firstMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match secondMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    published = .mu publishedEntry publishedBody publishedDepth publishedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal publishedDepth publishedOrdinary = true := by cbv
run_cmd do
  (← IO.getStderr).putStrLn "STAGE new_record"
  (← IO.getStderr).flush
private theorem new_record : heap.nodeRecords publishedEntry.key = none ∧
    firstAfter.nodeRecords publishedEntry.key = some published := by cbv
private theorem changed : heap ≠ firstAfter := by
  intro same
  have records := congrArg (fun state : Heap => state.nodeRecords publishedEntry.key) same
  rw [new_record.1,new_record.2] at records
  cases records
run_cmd do
  (← IO.getStderr).putStrLn "STAGE semantic"
  (← IO.getStderr).flush
private theorem semantic : SemanticReady heap := SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap,built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
run_cmd do
  (← IO.getStderr).putStrLn "STAGE first_project"
  (← IO.getStderr).flush
private theorem first_project : Project [0] firstMu heap firstOutput firstAfter :=
  SourceEqualityProjectionWorkerSound.project_graph 8 8 [0] firstMu heap firstOutput firstAfter first_done
private theorem second_head : SourceEqualityRequiredHead.Head secondMu firstAfter secondExposed secondHeadAfter :=
  SourceEqualityRequiredWorkerSound.head_graph 8 secondMu firstAfter secondExposed secondHeadAfter second_head_done
private theorem second_body : Project [0] secondExposed secondHeadAfter secondOutput secondAfter :=
  SourceEqualityProjectionWorkerSound.project_graph 7 8 [0] secondExposed secondHeadAfter secondOutput secondAfter second_body_done
private theorem second_project : Project [0] secondMu firstAfter secondOutput secondAfter :=
  .recursive shapes.2.2.2.2.1 second_head second_body
run_cmd do
  (← IO.getStderr).putStrLn "STAGE scan"
  (← IO.getStderr).flush
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

run_cmd do
  (← IO.getStderr).putStrLn "STAGE canonical_row"
  (← IO.getStderr).flush
private theorem canonical_row : (nodeEdges result)[1]? = some row := by cbv
private theorem different_mu : firstMu ≠ secondMu := by cbv
private noncomputable def initial_history : PublicationHistory empty heap :=
  SourceCurrentNativeMuPublication.closed_history expression
private noncomputable def initial_issued : SourceCurrentNativeMuIssuedHistory.Path empty heap :=
  SourceCurrentNativeMuIssuedHistory.closed_path expression
attribute [irreducible] built builtValue heap firstMu secondMu fallback branch0 branch1 rootEntry
  firstCalled firstOutput firstAfter firstHead firstExposed published publishedEntry publishedBody
  publishedDepth publishedOrdinary secondHead secondExposed secondHeadAfter secondBodyCalled
  secondOutput secondAfter firstRow row called result after terminal observed readAfter

run_cmd do
  (← IO.getStderr).putStrLn "STAGE first_available"
  (← IO.getStderr).flush
private theorem first_available : Available heap firstMu :=
  available.children firstMu (by
    change firstMu ∈ branch0.children ++ (branch1.children ++ [])
    rw [shapes.1,shapes.2.1]
    exact .head _)
private theorem second_available : Available heap secondMu :=
  available.children secondMu (by
    change secondMu ∈ branch0.children ++ (branch1.children ++ [])
    rw [shapes.1,shapes.2.1]
    exact .tail _ (.head _))
run_cmd do
  (← IO.getStderr).putStrLn "STAGE frame"
  (← IO.getStderr).flush
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
  canonical := canonical_row
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
  sourceSelected := rfl
  childSelected := by rw [shapes.2.1]; rfl
  projectPrefix := .selected (by rw [shapes.1]; rfl) first_project .nil
  call := second_project
  projectSuffix := .nil
  rest := by
    have effects := SourceEqualityProjectionCosts.project_effects first_project semantic costs first_available
    exact SourceCurrentProjectionReadSpine.project second_project effects.2.1 effects.2.2.1
      (effects.1.available secondMu second_available) second_read 0 row rfl
run_cmd do
  (← IO.getStderr).putStrLn "STAGE located"
  (← IO.getStderr).flush
private theorem located : Entry project read 1 row [0] secondMu :=
  .ordinary frame 0 rfl (by change select branch1.children 0 = some secondMu; rw [shapes.2.1]; rfl)
    (.head (recursive := shapes.2.2.2.2.1) (head := second_head) (body := second_body) frame.rest)
run_cmd do
  (← IO.getStderr).putStrLn "STAGE supported"
  (← IO.getStderr).flush
private theorem supported : ∃ observation : SourceCurrentRecursiveEntryObservation.Observation secondMu row,
    [0,0] = ([0] : List Nat).map Int.ofNat ++ observation.path ∧
    Keeps heap observation.before ∧ Keeps observation.reader after ∧
    Nonempty (PublicationHistory heap observation.before) := by
  have effects := SourceEqualityProjectionCosts.project_effects project semantic costs available
  have readerGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain project semantic costs available guards
  exact SourceCurrentRecursiveEntryPublication.entry located semantic costs available guards effects.2.1 effects.2.2.1
    (pure_keeps after effects.2.1.ready) readerGuards

run_cmd do
  (← IO.getStderr).putStrLn "STAGE site_root"
  (← IO.getStderr).flush
private theorem site_root {path value before output later}
    {actual : Project path value before output later}
    {reader edges readFinish position selectedRow} {read : Read output reader edges readFinish} {needle current}
    {entry : Entry actual read position selectedRow [] needle}
    (site : SourceCurrentRecursiveEntryPublicationSites.Site entry current) : value = needle ∧ before = current := by
  cases site with
  | root => exact ⟨rfl,rfl⟩
  | head => exact ⟨rfl,rfl⟩
run_cmd do
  (← IO.getStderr).putStrLn "STAGE prefix_unique"
  (← IO.getStderr).flush
private theorem prefix_unique {edge : Row} {child : Node} {before endpoint : Heap} {output : Node}
    (selected : select edge.children 0 = some child) (call : Project [0] child before output endpoint)
    {values current} (actual : ProjectRows [0] 0 [edge] before values current) : current = endpoint := by
  cases actual with
  | missing absent rest =>
    rw [selected] at absent
    cases absent
  | selected found first rest =>
    have same := Option.some.inj (found.symm.trans selected)
    cases same
    cases rest
    exact (SourceEqualityProjectionAPI.node_unique first call).2
run_cmd do
  (← IO.getStderr).putStrLn "STAGE pair_site"
  (← IO.getStderr).flush
private theorem pair_site {firstRow secondRow : Row} {firstChild secondChild : Node}
    {sourceEntry depth free before result after}
    {actual : Project [0,0] (.node sourceEntry [firstRow,secondRow] depth free) before result after}
    {reader rows readFinish position selectedRow} {read : Read result reader rows readFinish}
    (firstChildren : firstRow.children = [firstChild]) (different : firstChild ≠ secondChild)
    {firstValue firstAfter} (firstCall : Project [0] firstChild before firstValue firstAfter)
    {located : Entry actual read position selectedRow [0] secondChild} {current}
    (site : SourceCurrentRecursiveEntryPublicationSites.Site located current) : current = firstAfter := by
  cases site with
  | @ordinary index path sourceEntry edges depth free before output later actual reader readRows readFinish
      position selectedRow read otherFrame childIndex signed chosen initialPath needle rest current selected =>
    have exactChild := site_root selected
    have sourceOne : otherFrame.sourceIndex = 1 := by
      cases sourceIndex : otherFrame.sourceIndex with
      | zero =>
        have sourceRow : otherFrame.sourceRow = firstRow := by
          simpa only [sourceIndex,List.getElem?_cons_zero,Option.some.injEq] using otherFrame.sourceSelected.symm
        have found := otherFrame.childSelected
        rw [sourceRow,firstChildren] at found
        change some firstChild = some otherFrame.child at found
        have same : firstChild = secondChild := (Option.some.inj found).trans exactChild.1
        exact False.elim (different same)
      | succ index =>
        cases index with
        | zero => exact sourceIndex
        | succ index =>
          have impossible := otherFrame.sourceSelected
          simp only [sourceIndex,List.getElem?_cons_succ,List.getElem?_nil] at impossible
          cases impossible
    have earlier : ProjectRows [0] 0 [firstRow] before
        (otherFrame.values.take otherFrame.operandIndex) otherFrame.start := by
      simpa only [sourceOne,List.take_succ_cons,List.take_zero] using otherFrame.projectPrefix
    have selected : select firstRow.children 0 = some firstChild := by rw [firstChildren]; rfl
    exact exactChild.2.symm.trans (prefix_unique selected firstCall earlier)
run_cmd do
  (← IO.getStderr).putStrLn "STAGE site_exact"
  (← IO.getStderr).flush
private theorem site_exact {current}
    (site : SourceCurrentRecursiveEntryPublicationSites.Site located current) : current = firstAfter := by
  exact pair_site shapes.1 different_mu first_project site

run_cmd do
  (← IO.getStderr).putStrLn "STAGE captured"
  (← IO.getStderr).flush
private theorem captured : ∃ observation : SourceCurrentRecursiveEntryObservation.Observation secondMu row,
    [0,0] = ([0] : List Nat).map Int.ofNat ++ observation.path ∧
    Keeps heap observation.before ∧ Keeps observation.reader after ∧
    Nonempty (PublicationHistory heap observation.before) ∧
    SourceCurrentRecursiveEntryPublicationSites.Site located observation.before ∧
    observation.before = firstAfter ∧ observation.path = [0] ∧
    observation.before.nodeRecords publishedEntry.key = some published ∧
    SourceCurrentNativeMuPublication.Written heap publishedEntry.key published ∧
    SourceCurrentNativeMuPublication.Written empty publishedEntry.key published := by
  have effects := SourceEqualityProjectionCosts.project_effects project semantic costs available
  have readerGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain project semantic costs available guards
  obtain ⟨observation,splitPath,first,last,⟨interval⟩,site⟩ :=
    SourceCurrentRecursiveEntryPublicationSites.entry located semantic costs available guards effects.2.1 effects.2.2.1
      (pure_keeps after effects.2.1.ready) readerGuards
  have exactBefore := site_exact site
  have remaining : observation.path = [0] := by simpa using splitPath.symm
  have present : observation.before.nodeRecords publishedEntry.key = some published := by
    rw [exactBefore]
    exact new_record.2
  have exactPresent : observation.before.nodeRecords publishedEntry.key =
      some (.mu publishedEntry publishedBody publishedDepth publishedOrdinary) := by
    rw [←shapes.2.2.2.2.2.2.2.1]
    exact present
  have localWriter : SourceCurrentNativeMuPublication.Written heap publishedEntry.key published := by
    rcases interval.writers publishedEntry.key publishedEntry publishedBody publishedDepth publishedOrdinary exactPresent with old | writer
    · rw [new_record.1] at old
      cases old
    · simpa only [←shapes.2.2.2.2.2.2.2.1] using writer
  have whole : PublicationHistory empty observation.before := .trans initial_history interval
  have globalWriter : SourceCurrentNativeMuPublication.Written empty publishedEntry.key published := by
    simpa only [←shapes.2.2.2.2.2.2.2.1] using
      whole.from_empty publishedEntry.key publishedEntry publishedBody publishedDepth publishedOrdinary exactPresent
  exact ⟨observation,splitPath,first,last,⟨interval⟩,site,exactBefore,remaining,present,localWriter,globalWriter⟩

run_cmd do
  (← IO.getStderr).putStrLn "STAGE checked_witness"
  (← IO.getStderr).flush
private theorem checked_witness :
    built = .done root heap ∧ SemanticReady heap ∧ Available heap root ∧
    Nonempty (PublicationHistory empty heap) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty heap) ∧
    Recursive firstMu ∧ Recursive secondMu ∧
    (match firstMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match secondMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    firstCalled = .done firstOutput firstAfter ∧
    called = .done result after ∧ terminal = .done observed readAfter ∧ observed = [firstRow,row] ∧
    frame.sourceIndex = 1 ∧ frame.operandIndex = 1 ∧ frame.readIndex = 0 ∧
    Entry project read 1 row [0] secondMu ∧
    heap ≠ firstAfter ∧ heap.nodeRecords publishedEntry.key = none ∧
    published = .mu publishedEntry publishedBody publishedDepth publishedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal publishedDepth publishedOrdinary = true ∧
    ∃ observation : SourceCurrentRecursiveEntryObservation.Observation secondMu row,
      [0,0] = ([0] : List Nat).map Int.ofNat ++ observation.path ∧
      Keeps heap observation.before ∧ Keeps observation.reader after ∧
      Nonempty (PublicationHistory heap observation.before) ∧
      SourceCurrentRecursiveEntryPublicationSites.Site located observation.before ∧
      observation.before = firstAfter ∧ observation.path = [0] ∧
      observation.before.nodeRecords publishedEntry.key = some published ∧
      SourceCurrentNativeMuPublication.Written heap publishedEntry.key published ∧
      SourceCurrentNativeMuPublication.Written empty publishedEntry.key published := by
  exact ⟨built_done,semantic,available,⟨initial_history⟩,⟨initial_issued⟩,
    shapes.2.2.2.1,shapes.2.2.2.2.1,shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,
    first_done,called_done,terminal_done,shapes.2.2.1,rfl,rfl,rfl,located,changed,new_record.1,
    shapes.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2,captured⟩

/-- A real non-root recursive observation retains an earlier newly published nested Mu. -/
theorem nonroot_publication :
    built = .done root heap ∧ SemanticReady heap ∧ Available heap root ∧
    Nonempty (PublicationHistory empty heap) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty heap) ∧
    Recursive firstMu ∧ Recursive secondMu ∧
    (match firstMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match secondMu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    firstCalled = .done firstOutput firstAfter ∧
    called = .done result after ∧ terminal = .done observed readAfter ∧ observed = [firstRow,row] ∧
    frame.sourceIndex = 1 ∧ frame.operandIndex = 1 ∧ frame.readIndex = 0 ∧
    Entry project read 1 row [0] secondMu ∧
    heap ≠ firstAfter ∧ heap.nodeRecords publishedEntry.key = none ∧
    published = .mu publishedEntry publishedBody publishedDepth publishedOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal publishedDepth publishedOrdinary = true ∧
    ∃ observation : SourceCurrentRecursiveEntryObservation.Observation secondMu row,
      [0,0] = ([0] : List Nat).map Int.ofNat ++ observation.path ∧
      Keeps heap observation.before ∧ Keeps observation.reader after ∧
      Nonempty (PublicationHistory heap observation.before) ∧
      SourceCurrentRecursiveEntryPublicationSites.Site located observation.before ∧
      observation.before = firstAfter ∧ observation.path = [0] ∧
      observation.before.nodeRecords publishedEntry.key = some published ∧
      SourceCurrentNativeMuPublication.Written heap publishedEntry.key published ∧
      SourceCurrentNativeMuPublication.Written empty publishedEntry.key published := checked_witness

run_cmd do
  (← IO.getStderr).putStrLn "STAGE finished"
  (← IO.getStderr).flush
end MicroCFTA.ObservedPublicationKernels
