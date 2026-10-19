import MicroCFTA.SourceCurrentProjectionPathOrigins
import MicroCFTA.SourceCurrentRecursiveEntryObservation
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

/-!
# A deep selected row has a path origin and no root origin

An actual source builds an event wrapper around a two-row ordinary node.
Projection selects its Mu child. The outer selected row index is one.
The actual Mu read index is zero. The path origin is [0,0].
The selected row has no epsilon origin at the event root.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ProjectionPathOriginKernels
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
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def finiteSource : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def muSource : Syntax Symbol Guard := .binder false (.node [.mk ("rec",.top) plain [.var 0]])
private def innerExpression : Syntax Symbol Guard := .node
  [.mk ("branch0",.top) plain [finiteSource],.mk ("branch1",.top) plain [muSource]]
private def expression : Syntax Symbol Guard := .node [.mk ("event",.top) plain [innerExpression]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def builtValue : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def rootValue : Node := (children builtValue)[0]?.getD .empty
private def finite : Node := (children rootValue)[0]?.getD .empty
private def mu : Node := (children rootValue)[1]?.getD .empty
private def fallback : Row := (run (makeEdge ("unused",.top) plain []) heap).1
private def branch0 : Row := (nodeEdges rootValue)[0]?.getD fallback
private def branch1 : Row := (nodeEdges rootValue)[1]?.getD fallback
private def leafRow : Row := (nodeEdges finite)[0]?.getD fallback
private def rootEntry := match rootValue with | .node entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def root : Node := .node rootEntry [branch0,branch1] rootValue.depth rootValue.free
private def eventRow : Row := (nodeEdges builtValue)[0]?.getD fallback
private def eventEntry := match builtValue with | .node entry _ _ _ => entry | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def event : Node := .node eventEntry [eventRow] builtValue.depth builtValue.free
private def muRead := MergedFreshOrdinaryExposure.nodeEdges 8 mu heap
private def muAfter : Heap := match muRead with | .done _ state => state | _ => heap
private def muRows : List Row := match muRead with | .done values _ => values | _ => []
private def row : Row := muRows[0]?.getD fallback
private def called := SourceEqualityProjectionWorker.project 8 8 [0] root heap
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after : Heap := match called with | .done _ state => state | _ => heap
private def terminal := MergedFreshOrdinaryExposure.nodeEdges 8 result after
private def observed : List Row := match terminal with | .done values _ => values | _ => []
private def readAfter : Heap := match terminal with | .done _ state => state | _ => after
private theorem built_done : built = .done event heap := by cbv
private theorem shapes : (nodeEdges root) = [branch0,branch1] ∧ branch0.children = [finite] ∧
    branch1.children = [mu] ∧ (nodeEdges finite) = [leafRow] ∧ muRows = [row] ∧
    observed = [leafRow,row] ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv
private theorem mu_done : muRead = .done [row] muAfter := by cbv
private theorem called_done : called = .done result after := by cbv
private theorem terminal_done : terminal = .done observed readAfter := by cbv
private theorem scan : ProjectRows [] 0 [branch0,branch1] heap [finite,mu] heap :=
  .selected (by cbv) .root (.selected (by cbv) .root .nil)
private theorem finiteRead : Read finite heap [leafRow] heap := .done 8 (by cbv)
private theorem recursiveRead : Read mu heap [row] muAfter := .done 8 mu_done
private theorem reads : ReadAll [finite,mu] heap [leafRow,row] muAfter :=
  .cons finiteRead (.cons recursiveRead .nil)
private theorem united : run (makeNode [leafRow,row]) muAfter = (result,after) := by cbv
private theorem project : Project [0] root heap result after :=
  .ordinary (entry := rootEntry) (depth := root.depth) (free := root.free) scan (.node reads united)
private theorem read : Read result after observed readAfter := .done 8 terminal_done
private def frame : ProjectionFrame project read 1 row where
  values := [finite,mu]
  middle := heap
  allRows := [leafRow,row]
  unionMiddle := muAfter
  projects := scan
  reads := reads
  built := united
  exactProject := rfl
  selected := by rw [shapes.2.2.2.2.2.1]; rfl
  canonical := by cbv
  rawIndex := 1
  raw := rfl
  operandIndex := 1
  operand := mu
  operandSelected := rfl
  earlierRows := [leafRow]
  selectedRows := [row]
  laterRows := []
  readStart := heap
  readFinish := muAfter
  readPrefix := .cons finiteRead .nil
  operandRead := recursiveRead
  readSuffix := .nil
  parts := rfl
  readIndex := 0
  readSelected := rfl
  sourceIndex := 1
  sourceRow := branch1
  child := mu
  start := heap
  finish := heap
  sourceSelected := by cbv
  childSelected := by cbv
  projectPrefix := .selected (by cbv) .root .nil
  call := .root
  projectSuffix := .nil
  rest := .root recursiveRead 0 row rfl
private theorem semantic : SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression event heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [heap,built] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available heap root := by
  have original := (InternedFreshOrdinaryFacts.closed_verified expression).result event heap built_done
  exact original.children root (by cbv; exact List.mem_cons_self)
private theorem occurrence : SourceCurrentClassRecursiveValueOrigins.Occurs event [0] root :=
  .child 0 0 eventRow root rfl (by cbv) (.root root)
private theorem path_origin : SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0] root row := by
  have effects := SourceEqualityProjectionCosts.project_effects project semantic costs available
  exact SourceCurrentProjectionPathOrigins.project_read project read 1 row
    (SourceCurrentProjectionReadSpine.Spine.ordinary read 1 row frame.selected frame.canonical
      frame.rawIndex frame.raw frame.operandIndex frame.operand frame.operandSelected
      frame.earlierRows frame.selectedRows frame.laterRows frame.readStart frame.readFinish
      frame.readPrefix frame.operandRead frame.readSuffix frame.parts frame.readIndex frame.readSelected
      frame.sourceIndex frame.sourceRow frame.child frame.start frame.finish frame.sourceSelected frame.childSelected
      frame.projectPrefix frame.call frame.projectSuffix frame.rest)
    semantic costs available effects.2.1 effects.2.2.1 (pure_keeps after effects.2.1.ready)
    readAfter (grows_refl readAfter)
private theorem combined : SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0,0] event row := by
  exact SourceCurrentProjectionPathOrigins.occurs occurrence path_origin
private theorem no_root_origin : ¬ MergedFreshOrdinaryGraph.Origin readAfter [event] row := by
  intro origin
  have member := (MergedFreshOrdinaryGraph.origin_node readAfter eventEntry [eventRow]
    builtValue.depth builtValue.free row).mp origin
  have different : row.entry.key.symbol ≠ eventRow.entry.key.symbol := by cbv
  exact different (congrArg (fun edge : Row => edge.entry.key.symbol) (List.mem_singleton.mp member))

private theorem checked_witness :
    built = .done event heap ∧ SemanticReady heap ∧ Available heap root ∧
    (nodeEdges root).length = 2 ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    called = .done result after ∧ terminal = .done observed readAfter ∧ observed = [leafRow,row] ∧
    observed[1]? = some row ∧ muRead = .done [row] muAfter ∧
    frame.sourceIndex = 1 ∧ frame.operandIndex = 1 ∧ frame.readIndex = 0 ∧
    SourceCurrentClassRecursiveValueOrigins.Occurs event [0] root ∧
    SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0] root row ∧
    SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0,0] event row ∧
    ¬ MergedFreshOrdinaryGraph.Origin readAfter [event] row := by
  exact ⟨built_done,semantic,available,by rw [shapes.1]; rfl,shapes.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2,called_done,terminal_done,shapes.2.2.2.2.2.1,
    by rw [shapes.2.2.2.2.2.1]; rfl,mu_done,rfl,rfl,rfl,occurrence,path_origin,combined,no_root_origin⟩

/-- An actual deep selected row has a composed path origin and no epsilon origin at its event root. -/
theorem deep_path :
    built = .done event heap ∧ SemanticReady heap ∧ Available heap root ∧
    (nodeEdges root).length = 2 ∧ Recursive mu ∧
    (match mu with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    called = .done result after ∧ terminal = .done observed readAfter ∧ observed = [leafRow,row] ∧
    observed[1]? = some row ∧ muRead = .done [row] muAfter ∧
    frame.sourceIndex = 1 ∧ frame.operandIndex = 1 ∧ frame.readIndex = 0 ∧
    SourceCurrentClassRecursiveValueOrigins.Occurs event [0] root ∧
    SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0] root row ∧
    SourceCurrentProjectionPathOrigins.PathOrigin readAfter [0,0] event row ∧
    ¬ MergedFreshOrdinaryGraph.Origin readAfter [event] row := checked_witness
end MicroCFTA.ProjectionPathOriginKernels
