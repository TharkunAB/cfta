import MicroCFTA.SourceCurrentNativeRowKeyable
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.NativeRowKeyableKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand IntersectSchedule SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
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
private def recursive : Syntax Symbol Guard := .binder true (.node [.mk ("loop",.top) top [.var 0]])
private def first : Syntax Symbol Guard := .node [.mk ("kept",.top) top [recursive]]
private def second : Syntax Symbol Guard := .node [.mk ("kept",.top) top [recursive],.mk ("other",.top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [first,second]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 130 := ⟨initial 130 machine,operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private theorem constructed : built = .done root heap := by cbv
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,first,second,recursive,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩,semantic.ready,loaded.1,?_⟩
  intro key row found
  rw [guarded key row found]
  exact loaded.2.2
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private def row : EdgeValue Symbol Guard := match left with
  | .node _ (selected :: _) _ _ => selected
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private theorem row_selected : (nodeEdges left)[0]? = some row := by cbv
private theorem literal : execute 64 control before = .done left (execute 64 control before).state := by cbv
private theorem branch : SourceRecursiveIntersectionControl.decision request.domain.key left right = .ordinary := by cbv

private def SelectedClaim : Prop :=
  built = .done root heap ∧ Good before ∧ left ≠ right ∧
  SourceRecursiveIntersectionControl.decision request.domain.key left right = .ordinary ∧
  row.children.map Value.referenceOf = [.mu 2] ∧
  ∃ fuel after,
    Trace fuel control before (.code (.pure left)) after ∧ (nodeEdges left)[0]? = some row ∧
    ∃ firstInput secondInput key,
      IntersectionFlatMemoKey.input left.referenceOf = some firstInput ∧
      IntersectionFlatMemoKey.input right.referenceOf = some secondInput ∧
      SourceRecursiveIntersectionMemo.requestKey 130 request.domain left right = some key

private theorem selected_checked : SelectedClaim := by
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
  have same := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (fuel+1) 64 control before
    after (execute 64 control before).state value left receipt.done literal
  rcases same with ⟨rfl,rfl⟩
  have different : left ≠ right := by
    intro equal
    have lengths := congrArg (fun value => (nodeEdges value).length) equal
    cbv at lengths
  exact ⟨constructed,initial_good,different,branch,by cbv,
    fuel,_,receipt.trace,row_selected,SourceCurrentNativeRowKeyable.selected request fuel left receipt.trace 0 row row_selected⟩

private def unresolved : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,.reference .depth,.empty⟩
private theorem missing : SourceRecursiveIntersectionMemo.requestKey 130 unresolved.domain unresolved.left unresolved.right = none := rfl
private theorem unresolved_trace : Trace 1 (.code (requestNode unresolved.domain unresolved.left unresolved.right)) before
    (.code (.pure (.empty : Value Symbol Guard))) before := by
  have inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
      (.code (requestNode unresolved.domain unresolved.left unresolved.right)) before := by
    refine ⟨⟨empty_domain _,InternedNestedProvenance.depth_available _,empty_available _⟩,?_⟩
    intro key impossible
    rw [missing] at impossible
    cases impossible
  exact .cons _ _ _ _ _ _ 0 inputs rfl (.refl _ _)

/-- A source-built distinct ordinary join with a recursive child derives its actual native key. -/
theorem selected_nested_source :
  built = .done root heap ∧ Good before ∧ left ≠ right ∧
  SourceRecursiveIntersectionControl.decision request.domain.key left right = .ordinary ∧
  row.children.map Value.referenceOf = [.mu 2] ∧
  ∃ fuel after,
    Trace fuel control before (.code (.pure left)) after ∧ (nodeEdges left)[0]? = some row ∧
    ∃ firstInput secondInput key,
      IntersectionFlatMemoKey.input left.referenceOf = some firstInput ∧
      IntersectionFlatMemoKey.input right.referenceOf = some secondInput ∧
      SourceRecursiveIntersectionMemo.requestKey 130 request.domain left right = some key := selected_checked

/-- A source-built checked heap admits an unkeyed Depth request only with its literal Empty return. -/
theorem unresolved_empty : built = .done root heap ∧ Good before ∧
    SourceRecursiveIntersectionMemo.requestKey 130 unresolved.domain unresolved.left unresolved.right = none ∧
    Trace 1 (.code (requestNode unresolved.domain unresolved.left unresolved.right)) before
      (.code (.pure (.empty : Value Symbol Guard))) before ∧
    (.empty : Value Symbol Guard) = .empty :=
  ⟨constructed,initial_good,missing,unresolved_trace,
    SourceCurrentNativeRowKeyable.unkeyed_empty unresolved 1 .empty missing unresolved_trace⟩

end MicroCFTA.NativeRowKeyableKernels
