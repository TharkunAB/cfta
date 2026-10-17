import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputFinite
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ClassOriginKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
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
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) top [
  .node [.mk ("a", .top) top [], .mk ("b", .top) top []],
  .node [.mk ("a", .top) top [], .mk ("c", .top) top []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def operations := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def before : Checked 10 := ⟨initial 10 machine, operations⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression, SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))


private theorem closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv
private def row : EdgeValue Symbol Guard := match left with
  | .node _ (first :: _) _ _ => first
  | _ => (run (makeEdge ("unused", .top) top []) empty).1
private def answer : Value Symbol Guard := (run (makeNode [row]) heap).1
private def control : Control (Value Symbol Guard) := .code (requestNode request.domain left right)
private noncomputable def reached : Checked 10 := (execute 8 control before).state
private theorem evaluated : execute 8 control before = .done answer reached := by cbv
private theorem row_selected : (nodeEdges answer)[0]? = some row := by cbv
private theorem ordinary : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary := by cbv

private theorem cold : ∃ fuel, Trace fuel control before (.code (.pure answer)) reached := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel,value,after,receipt,_⟩ := SourceCurrentAllocatedFiniteOrdinaryOutputFinite.cold
    8 2 0 1 (fun _ _ => true) before initial_good semantic rfl left right originals.1 originals.2
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
  have first := done_stable (fuel + 1) 8 control before after value (trace_done fuel control before after value receipt.trace.steps)
  have second := done_stable 8 (fuel + 1) control before reached answer evaluated
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (first.symm.trans (by simpa only [Nat.add_comm] using second))
  exact ⟨fuel,receipt.trace⟩

private theorem route_ordinary {reader : Checked 10} {result : Value Symbol Guard}
    {terminal : NodeRequest Symbol Guard}
    (route : SourceCurrentNativeQueryRowOrigins.Route reader result request terminal) : terminal = request := by
  cases route with
  | refl => rfl
  | step one rest =>
      obtain ⟨_,_,_,_,_,_,forwarded,_⟩ := one
      rcases forwarded with ⟨swap,_⟩ | ⟨restart,_⟩
      · rw [ordinary] at swap; cases swap
      · rw [ordinary] at restart; cases restart

private theorem joined_of_origin {reader : Checked 10}
    (origin : SourceCurrentNativeQueryRowOrigins.RowOrigin reader request answer 0 row) :
    SourceCurrentNativeQueryRowOrigins.Joined reader request row := by
  obtain ⟨terminal,_,route,_,_,source⟩ := origin
  have same := route_ordinary route
  subst terminal
  rw [ordinary] at source
  rcases source with ⟨impossible,_⟩ | ⟨_,joined⟩ | residual
  · cases impossible
  · exact joined
  · simp only [SourceCurrentNativeQueryRowOrigins.Residual] at residual
    rcases residual with h | h | h | h | h | h | h <;> cases h

/-- A cold zero-child join and its exact warm replay derive actual full-guard source writers. -/
private theorem checked_zero_child_join_cold_warm :
    built = .done root heap ∧ Available heap left ∧ Available heap right ∧ left ≠ right ∧
    row.children = [] ∧ (nodeEdges answer)[0]? = some row ∧
    ∃ fuel handle key,
      Trace fuel control before (.code (.pure answer)) reached ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin reached request answer 0 row ∧
      SourceCurrentNativeQueryRowOrigins.Joined reached request row ∧
      reached.native.nodes.table key = some handle ∧
      reached.native.nodes.cells handle = some ⟨request,.returned answer⟩ ∧
      Trace 1 control reached (.code (.pure answer)) reached ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin reached request answer 0 row ∧
      SourceCurrentNativeQueryRowOrigins.Joined reached request row := by
  obtain ⟨fuel,actual⟩ := cold
  have initialHistory : SourceCurrentNativeEdgeWriterGrowth.History before := .initial machine operations
  have origin := SourceCurrentNativeQueryRowOrigins.request request fuel answer initial_good initialHistory
    closed.1 closed.2 actual 0 row row_selected
  have keySome : ∃ key, SourceRecursiveIntersectionMemo.requestKey 10 request.domain left right = some key := by
    have some : (SourceRecursiveIntersectionMemo.requestKey 10 request.domain left right).isSome = true := by cbv
    cases key : SourceRecursiveIntersectionMemo.requestKey 10 request.domain left right with
    | none => rw [key] at some; cases some
    | some value => exact ⟨value,rfl⟩
  obtain ⟨key,keyEq⟩ := keySome
  change SourceRecursiveIntersectionMemo.requestKey 10 request.domain request.left request.right = some key at keyEq
  obtain ⟨⟨handle,published,present⟩,_⟩ := SourceCurrentAllocatedNativeCompletedMemo.repeat_of_trace
    fuel request before reached answer initial_good.native key keyEq actual
  have ready : NodeReady reached.native.machine request := (origin.2.1.native.nodes.checked handle _ present).1
  have safe : SourceRecursiveIntersectionMemo.KeySafe 10 request.domain left right := by
    unfold SourceRecursiveIntersectionMemo.KeySafe
    refine ⟨by decide,by cbv,.node 0,.node 1,?_,?_,?_,?_⟩ <;> cbv
  have selected : lookupNode 10 request reached.native = (.memoized handle,reached.native) := by
    simp only [lookupNode,keyEq,FlatMemoThunk.lookupOrInsert,published]
  have demanded : demandNode handle reached.native = (.ready answer,reached.native) := by
    simp only [demandNode,FlatMemoThunk.demand,present]
  have one : step control reached = .yielded (.code (.pure answer)) reached := by
    change lift reached.operations (SourceRecursiveIntersectionNative.step
      SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin (.node request .pure) reached.native) = _
    simp only [SourceRecursiveIntersectionNative.step,selected,demanded,lift]
  have warm : Trace 1 control reached (.code (.pure answer)) reached :=
    .cons _ _ _ _ _ _ 0 ⟨ready,fun _ _ => safe⟩ one (.refl _ _)
  have again := SourceCurrentNativeQueryRowOrigins.request request 1 answer origin.2.1 origin.1 closed.1 closed.2 warm 0 row row_selected
  refine ⟨constructed,originals.1,originals.2,?_,(by cbv),row_selected,fuel,handle,key,actual,origin.2.2.2,
    joined_of_origin origin.2.2.2,published,present,warm,again.2.2.2,joined_of_origin again.2.2.2⟩
  intro same
  have identities := congrArg Value.referenceOf same
  cbv at identities
  cases identities


private def selfRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,left⟩
private def selfControl : Control (Value Symbol Guard) := .code (requestNode selfRequest.domain left left)
private noncomputable def selfReached : Checked 10 := (execute 3 selfControl before).state
private theorem self_evaluated : execute 3 selfControl before = .done left selfReached := by cbv

/-- An initial source self query captures and returns its literal row without a joined-row premise. -/
private theorem checked_initial_self :
    built = .done root heap ∧ Available heap left ∧ left.free = [] ∧
    SourceRecursiveIntersectionControl.decision selfRequest.domain.key selfRequest.left selfRequest.right = .self ∧
    ∃ fuel handle,
      Trace fuel selfControl before (.code (.pure left)) selfReached ∧
      selfReached.native.nodes.cells handle = some ⟨selfRequest,.returned left⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := 10) handle selfRequest left selfReached.native ∧
      (nodeEdges left)[0]? = some row ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin selfReached selfRequest left 0 row := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  obtain ⟨fuel,value,after,receipt,_⟩ := SourceCurrentAllocatedFiniteOrdinaryOutputFinite.cold
    8 2 0 1 (fun _ _ => true) before initial_good semantic rfl left left originals.1 originals.1
    (by cbv) (by cbv) (by cbv) (by cbv) (by cbv)
  have first := done_stable (fuel + 1) 3 selfControl before after value
    (trace_done fuel selfControl before after value receipt.trace.steps)
  have second := done_stable 3 (fuel + 1) selfControl before selfReached left self_evaluated
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (first.symm.trans (by simpa only [Nat.add_comm] using second))
  have history : SourceCurrentNativeEdgeWriterGrowth.History before := .initial machine operations
  have selected : (nodeEdges left)[0]? = some row := by cbv
  have produced := SourceCurrentNativeQueryRowOrigins.request selfRequest fuel left initial_good history
    closed.1 closed.1 receipt.trace 0 row selected
  have origin := SourceCurrentSharedLeafNativeLineage.request selfRequest fuel left initial_good history receipt.trace
  obtain ⟨handle,present,writer⟩ := origin.2.2.2.returned closed.1 closed.1
  exact ⟨constructed,originals.1,closed.1,(by cbv),fuel,handle,receipt.trace,present,writer,selected,produced.2.2.2⟩

/-- The exact checked source witness retains all states and origins. -/
theorem zero_child_join_cold_warm :
    built = .done root heap ∧ Available heap left ∧ Available heap right ∧ left ≠ right ∧
    row.children = [] ∧ (nodeEdges answer)[0]? = some row ∧
    ∃ fuel handle key,
      Trace fuel control before (.code (.pure answer)) reached ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin reached request answer 0 row ∧
      SourceCurrentNativeQueryRowOrigins.Joined reached request row ∧
      reached.native.nodes.table key = some handle ∧
      reached.native.nodes.cells handle = some ⟨request,.returned answer⟩ ∧
      Trace 1 control reached (.code (.pure answer)) reached ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin reached request answer 0 row ∧
      SourceCurrentNativeQueryRowOrigins.Joined reached request row := checked_zero_child_join_cold_warm

/-- The exact checked source witness retains all states and origins. -/
theorem initial_self :
    built = .done root heap ∧ Available heap left ∧ left.free = [] ∧
    SourceRecursiveIntersectionControl.decision selfRequest.domain.key selfRequest.left selfRequest.right = .self ∧
    ∃ fuel handle,
      Trace fuel selfControl before (.code (.pure left)) selfReached ∧
      selfReached.native.nodes.cells handle = some ⟨selfRequest,.returned left⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := 10) handle selfRequest left selfReached.native ∧
      (nodeEdges left)[0]? = some row ∧
      SourceCurrentNativeQueryRowOrigins.RowOrigin selfReached selfRequest left 0 row := checked_initial_self

end MicroCFTA.ClassOriginKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.ClassOriginKernels.zero_child_join_cold_warm
#print MicroCFTA.ClassOriginKernels.zero_child_join_cold_warm
#print axioms MicroCFTA.ClassOriginKernels.zero_child_join_cold_warm

#check @MicroCFTA.ClassOriginKernels.initial_self
#print MicroCFTA.ClassOriginKernels.initial_self
#print axioms MicroCFTA.ClassOriginKernels.initial_self

