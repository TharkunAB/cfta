import MicroCFTA.SourceCurrentNativeOriginExposure
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.NativeOriginExposureKernels
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeOriginExposure (Unfold Writer)
open MergedFreshOrdinaryGraph (Origin)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := SourceEqualityConstraintConstructors.top
private def first : Syntax Symbol Guard := .binder true
  (.node [.mk ("leaf",.top) top [],.mk ("loop",.top) top [.var 0]])
private def second : Syntax Symbol Guard := .binder true
  (.node [.mk ("leaf",.top) top [],.mk ("loop",.top) top [.var 0],.mk ("extra",.top) top []])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [first,second]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 130 := ⟨initial 130 machine,operations⟩
private def query : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control (Value Symbol Guard) := .code (requestNode query.domain left right)
private def row : EdgeValue Symbol Guard := ((nodeEdges (SourceRecursiveIntersectionKernel.body left))[0]?).getD
  (run (makeEdge ("fallback",.top) top []) empty).1
private def observed := execute 128 control before
private def reader := observed.state
private def unfolded := InternedFreshOrdinaryStoredSubstitution.unfold left reader.native.machine.heap
private def exposed : Value Symbol Guard := match unfolded with | .done value _ => value | .pending .. => .empty

private theorem constructed : built = .done root heap := by cbv
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,first,second,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩,semantic.ready,loaded.1,?_⟩
  intro key edge found
  rw [guarded key edge found]
  exact loaded.2.2
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private theorem branch : SourceRecursiveIntersectionControl.decision query.domain.key left right = .bothMu := by cbv
private theorem literal : observed = .done left reader := by cbv
private theorem unfolded_done : unfolded = .done exposed unfolded.state := by cbv
private theorem exposed_row : row ∈ nodeEdges exposed := by cbv; exact .head _
private theorem full_origin : Origin reader.native.machine.heap [left] row := by
  have next : exposed ∈ MergedFreshOrdinaryGraph.successors reader.native.machine.heap left := by
    have shape : (match left with | .mu .. => true | _ => false) = true := by cbv
    cases same : left with
    | mu entry body depth ordinary =>
        rw [MergedFreshOrdinaryGraph.successors]
        rw [← same]
        change exposed ∈ (match unfolded with | .done value _ => [value] | .pending .. => [])
        rw [unfolded_done]
        exact List.mem_singleton_self _
    | empty | reference | node | union => simp only [same,Bool.false_eq_true] at shape
  exact ⟨exposed,.step (.seed (List.mem_singleton_self _)) next,exposed_row⟩

private def Claim : Prop :=
  built = .done root heap ∧ Good before ∧ History before ∧ left ≠ right ∧
    SourceRecursiveIntersectionControl.decision query.domain.key left right = .bothMu ∧
    nodeEdges left = [] ∧ Origin reader.native.machine.heap [left] row ∧
    ∃ fuel,
      Trace fuel control before (.code (.pure left)) reader ∧
      History reader ∧ Good reader ∧ Grows heap reader.native.machine.heap ∧
      ∃ handle captured finished count entry storedBody depth ordinary,
        reader.native.nodes.cells handle = some ⟨query,.returned left⟩ ∧
        Good captured ∧ NodeReady captured.native.machine query ∧
        captured.native.nodes.cells handle = some ⟨query,.evaluating⟩ ∧
        Trace count (.code (compileNode query)) captured (.code (.pure left)) finished ∧
        SourceCurrentNativeMuBodyOrigins.Body reader count query captured left finished ∧
        left = .mu entry storedBody depth ordinary ∧
        .interned entry.identity ∈ storedBody.free ∧
        Unfold reader.native.machine.heap entry storedBody depth ordinary row

private theorem checked : Claim := by
  have facts := initial_good.native.machine.1
  have closedLeft : left.free = [] := by cbv
  have closedRight : right.free = [] := by cbv
  have originalLeft := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent available.1 closedLeft
  have originalRight := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent available.2 closedRight
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel,value,after,receipt,_,_,_,_,_,_,_,_⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 128 (fun _ _ => true) before initial_good semantic
      (SourceRecursiveIntersectionNative.idle_initial machine)
      left right originalLeft originalRight available.1 available.2 closedLeft closedRight
      (by cbv) (by cbv) (by cbv)
  have same := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (fuel+1) 128 control before
    after reader value left receipt.done literal
  rcases same with ⟨rfl,rfl⟩
  have history : History before := .initial machine operations
  obtain ⟨reached,good,growth,terminal,handle,route,cell,_,_,_,_,writer,exposure⟩ :=
    SourceCurrentNativeOriginExposure.request query fuel left initial_good history receipt.trace row full_origin
  have terminalSame : terminal = query := by
    cases route with
    | refl => rfl
    | step one rest =>
        obtain ⟨_,_,_,_,_,_,selected,_⟩ := one
        rcases selected with ⟨swap,_⟩ | ⟨reset,_⟩
        · change SourceRecursiveIntersectionControl.decision query.domain.key left right = _ at swap
          rw [branch] at swap; cases swap
        · change SourceRecursiveIntersectionControl.decision query.domain.key left right = _ at reset
          rw [branch] at reset; cases reset
  subst terminal
  obtain ⟨captured,finished,count,capturedGood,ready,owner,actual,_,_,_,_,_,body⟩ := writer
  have shape : ∃ entry storedBody depth ordinary, left = .mu entry storedBody depth ordinary ∧
      .interned entry.identity ∈ storedBody.free := by
    have tag : (match left with | .mu entry body _ _ => decide (.interned entry.identity ∈ body.free) | _ => false) = true := by cbv
    cases same : left <;> simp only [same,Bool.false_eq_true] at tag
    exact ⟨_,_,_,_,rfl,of_decide_eq_true tag⟩
  obtain ⟨entry,storedBody,depth,ordinary,shape,used⟩ := shape
  have different : left ≠ right := by
    intro equal
    have names := congrArg Value.referenceOf equal
    cbv at names
    cases names
  exact ⟨constructed,initial_good,history,different,branch,by cbv,full_origin,
    fuel,receipt.trace,reached,good,growth,handle,captured,finished,count,entry,storedBody,depth,ordinary,
    cell,capturedGood,ready,owner,actual,body (.inl branch),shape,used,exposure _ _ _ _ shape⟩

/-- Distinct actual used Mu operands return a retained Mu with no physical row and a complete epsilon origin. -/
theorem retained_used_mu :
  built = .done root heap ∧ Good before ∧ History before ∧ left ≠ right ∧
    SourceRecursiveIntersectionControl.decision query.domain.key left right = .bothMu ∧
    nodeEdges left = [] ∧ Origin reader.native.machine.heap [left] row ∧
    ∃ fuel,
      Trace fuel control before (.code (.pure left)) reader ∧
      History reader ∧ Good reader ∧ Grows heap reader.native.machine.heap ∧
      ∃ handle captured finished count entry storedBody depth ordinary,
        reader.native.nodes.cells handle = some ⟨query,.returned left⟩ ∧
        Good captured ∧ NodeReady captured.native.machine query ∧
        captured.native.nodes.cells handle = some ⟨query,.evaluating⟩ ∧
        Trace count (.code (compileNode query)) captured (.code (.pure left)) finished ∧
        SourceCurrentNativeMuBodyOrigins.Body reader count query captured left finished ∧
        left = .mu entry storedBody depth ordinary ∧
        .interned entry.identity ∈ storedBody.free ∧
        Unfold reader.native.machine.heap entry storedBody depth ordinary row := checked

end
end MicroCFTA.NativeOriginExposureKernels
