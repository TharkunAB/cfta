import MicroCFTA.SourceCurrentNativeQueryTerminalOrigins
import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact
import MicroCFTA.SourceCurrentAllocatedNativeInitialInstructionBudget
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.NativeTerminalOriginsKernels
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
private def base : Syntax Symbol Guard := .node [.mk ("base", .top) top []]
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  base, .binder false base,
  .union [.binder false base, .binder false (.node [.mk ("other",.top) top []])]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right (union : Bool) : Value Symbol Guard := ((children root)[if union then 2 else 1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 130 := ⟨initial 130 machine,operations⟩
private def request (union : Bool) : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right union⟩
private def control (union : Bool) : Control (Value Symbol Guard) := .code (requestNode (request union).domain left (right union))
private theorem constructed : built = .done root heap := by cbv
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,base,SourceEqualityAnnotationConstruction.Allowed,
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
private theorem available (union : Bool) : Available heap left ∧ Available heap (right union) := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact source.children left (by cbv; exact .head _)
  · cases union
    · exact source.children (right false) (by cbv; exact .tail _ (.head _))
    · exact source.children (right true) (by cbv; exact .tail _ (.tail _ (.head _)))
private def selected : EdgeValue Symbol Guard := match left with
  | .node _ (row :: _) _ _ => row
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private theorem selected_row : (nodeEdges left)[0]? = some selected := by cbv
private def Claim (union : Bool) : Prop :=
  built = .done root heap ∧
  SourceRecursiveIntersectionControl.decision (request union).domain.key left (right union) =
    (if union then .rightUnion else .rightMu) ∧
  ∃ fuel after,
    SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel (control union) before left after
      (fun final value => Available final.heap value) ∧
    SourceCurrentNativeQueryTerminalOrigins.Resolved after (request union) left 0 selected ∧
    ∃ handle, after.native.nodes.cells handle = some ⟨request union,.returned left⟩ ∧
      (if union then SourceCurrentNativeQueryTerminalOrigins.Union false after handle (request union) left selected
       else SourceCurrentNativeQueryTerminalOrigins.Mu after handle (request union) left)
private theorem literal (union : Bool) :
    execute 64 (control union) before = .done left (execute 64 (control union) before).state := by
  cases union <;> cbv
private theorem branch (union : Bool) :
    SourceRecursiveIntersectionControl.decision (request union).domain.key left (right union) =
      (if union then .rightUnion else .rightMu) := by cases union <;> cbv
private theorem closed_right (union : Bool) : (right union).free = [] := by cases union <;> cbv
private theorem run (union : Bool) : Claim union := by
  have facts := initial_good.native.machine.1
  have closedLeft : left.free = [] := by cbv
  have closedRight := closed_right union
  have originalLeft := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent (available union).1 closedLeft
  have originalRight := SourceRecursiveIntersectionOriginalOutput.closed_original (right union) heap facts.coherent (available union).2 closedRight
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel,value,after,receipt,_,_,_,_,_,_,_,_⟩ :=
    SourceCurrentAllocatedNativeInitialInstructionBudget.initial 128 (fun _ _ => true) before initial_good semantic
      (SourceRecursiveIntersectionNative.idle_initial machine)
      left (right union) originalLeft originalRight (available union).1 (available union).2 closedLeft closedRight
      (by cbv) (by cbv) (by cbv)
  have same := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (fuel+1) 64 (control union) before
    after (execute 64 (control union) before).state value left receipt.done (literal union)
  rcases same with ⟨rfl,rfl⟩
  have history : SourceCurrentNativeEdgeWriterGrowth.History before := .initial machine operations
  obtain ⟨reached,good,growth,resolved⟩ := SourceCurrentNativeQueryTerminalOrigins.request
    (request union) fuel left initial_good history closedLeft closedRight receipt.trace 0 selected selected_row
  obtain ⟨_,_,_,origin⟩ := SourceCurrentSharedLeafNativeLineage.request (request union) fuel left initial_good history receipt.trace
  obtain ⟨handle,present,_⟩ := origin.returned closedLeft closedRight
  refine ⟨constructed,branch union,fuel,_,receipt,resolved,handle,present,?_⟩
  · cases union
    · exact SourceCurrentNativeMuWriterOrigins.returned reached (request false) left handle present (.inr (.inr (branch false)))
    · have rowOrigin : MergedFreshOrdinaryGraph.Origin (execute 64 (control true) before).state.native.machine.heap [left] selected :=
        ⟨left,.seed (by simp),List.mem_of_getElem? selected_row⟩
      simpa only [SourceCurrentNativeQueryTerminalOrigins.Union,Bool.false_eq_true,ite_false,ite_true] using
        SourceCurrentNativeUnionWriterOrigins.right reached handle (request true) left present closedLeft closedRight (branch true) selected rowOrigin

/-- A source-built right-Mu query derives its actual schedule and selected row origin. -/
theorem actual_mu : Claim false := run false

/-- A source-built right-union query derives its actual ordered member call and selected row origin. -/
theorem actual_union : Claim true := run true

end MicroCFTA.NativeTerminalOriginsKernels
