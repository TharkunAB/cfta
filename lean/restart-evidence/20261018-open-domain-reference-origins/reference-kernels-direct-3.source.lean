import MicroCFTA.SourceCurrentNativeReferenceOrigins
import MicroCFTA.SourceCurrentNativeMuBodyOrigins
import MicroCFTA.SourceCurrentNativeAdmissionWriter
import MicroCFTA.SourceCurrentNativePublicationTrace
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NativeEnteredReferenceCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State 130
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def muPlan : Syntax Symbol Guard := .binder false (.node [.mk ("f",.top) plain [.var 0]])
private def otherPlan : Syntax Symbol Guard := .node [.mk ("f",.top) plain [.node [.mk ("leaf",.top) plain []]]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [muPlan,otherPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities Cache.emptyState
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : Checked :=
  ⟨initial 130 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private theorem built_done : built = .done root heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready checked := by
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [plain] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [plain] := by
    intro guard member
    have same : guard = plain := by
      simpa only [expression,muPlan,otherPlan,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,false_or,or_self] using member
    cases same
    exact List.mem_singleton_self _
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 130 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private def bound : Node := (children root)[0]?.getD .empty
private def other : Node := (children root)[1]?.getD .empty
private def leaf : Node := (children other)[0]?.getD .empty
private def boundId : Nat := (SourceRecursiveIntersectionControl.identity bound).getD 0
private def otherId : Nat := (SourceRecursiveIntersectionControl.identity other).getD 0
private def entered := SourceRecursiveIntersectionEnvironment.enter checked.native.machine.domains
  IntersectionEmptyDomain.emptyDomain.key other bound otherId boundId
private def outer : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,other,bound⟩
private def referenced : NodeRequest Symbol Guard := ⟨entered.1,leaf,.reference (.interned boundId)⟩
private theorem bound_available : Available heap bound :=
  source_available.children bound (by cbv; exact .head _)
private theorem other_available : Available heap other :=
  source_available.children other (by cbv; exact .tail _ (.head _))
private theorem bound_closed : bound.free = [] := by cbv
private theorem other_closed : other.free = [] := by cbv
private theorem bound_recursive : ∃ entry body depth ordinary, bound = .mu entry body depth ordinary := by
  have tag : (match bound with | .mu .. => true | _ => false) = true := by cbv
  cases found : bound <;> simp_all only [Bool.false_eq_true]
  exact ⟨_,_,_,_,rfl⟩
private theorem node_room : checked.native.machine.heap.nodes.next < 2 ^ 128 := by cbv
private theorem edge_room : checked.native.machine.heap.edges.next ≤ 2 ^ (128 + 2) := by cbv
private theorem domain_room : checked.native.machine.domains.next +
    2 ^ (checked.native.machine.heap.nodes.next + checked.native.machine.heap.nodes.next * checked.native.machine.heap.nodes.next) <
      2 ^ (128 + 1) := by cbv
private theorem initial_history : SourceCurrentNativeEdgeWriterGrowth.History checked := .initial _ _
private theorem source_publications : Nonempty (SourceCurrentNativeMuPublication.History empty heap) := by
  have emitted := SourceCurrentNativeMuPublication.build_history expression [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
  exact emitted
private def called := SourceEqualityNativeDemand.execute 128
  (.code (requestNode outer.domain outer.left outer.right)) checked
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := called.state
private theorem called_done : called = .done result after := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases observed : called <;> simp_all only [result,after,SourceEqualityNativeDemand.Outcome.state,Bool.false_eq_true]
private theorem result_empty : result = .empty := by cbv
private theorem mu_branch : SourceRecursiveIntersectionControl.decision outer.domain.key outer.left outer.right = .rightMu := by cbv
private theorem right_branch : SourceRecursiveIntersectionControl.decision referenced.domain.key referenced.left referenced.right = .rightReference := by cbv
private theorem swap_branch : SourceRecursiveIntersectionControl.decision entered.1.key (.reference (.interned boundId)) leaf = .swap := by cbv
private theorem reference_present : after.native.nodes.cells 4 = some ⟨referenced,.returned result⟩ := by cbv
private theorem actual_binding : SourcePreparedSharedRows.read heap boundId = some bound := by cbv
private theorem scope_present : boundId ∈ SourceRecursiveIntersectionDomain.names entered.1.key := by cbv; exact .head _
private theorem open_reference : referenced.right.free ≠ [] := by cbv; intro impossible; cases impossible
private def directRequest : NodeRequest Symbol Guard :=
  ⟨IntersectionEmptyDomain.emptyDomain,.reference (.uninterned 0),.empty⟩
private theorem direct_key : SourceRecursiveIntersectionMemo.requestKey 130 directRequest.domain
    directRequest.left directRequest.right = none := by cbv
private theorem direct_trace : Trace 1 (.code (requestNode directRequest.domain directRequest.left directRequest.right))
    checked (.code (.pure (.empty : Node))) checked := by
  apply SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.cons _ _ _ _ _ _ 0 ?_ ?_ (.refl _ _)
  · refine ⟨⟨SourceRecursiveIntersectionInputView.empty_domain _,
      InternedNestedProvenance.ordinary_available _ 0,empty_available _⟩,?_⟩
    intro key found
    rw [direct_key] at found
    cases found
  · cbv
private def MainClaim : Prop :=
  built = .done root heap ∧
  (∃ entry body depth ordinary, bound = .mu entry body depth ordinary) ∧
  bound.free = [] ∧ other.free = [] ∧
  Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
  SourceCurrentAllocatedNativePhysicalCompletion.Good checked ∧
  called = .done result after ∧ result = .empty ∧
  SourceRecursiveIntersectionControl.decision outer.domain.key outer.left outer.right = .rightMu ∧
  SourceRecursiveIntersectionControl.decision entered.1.key (.reference (.interned boundId)) leaf = .swap ∧
  SourceRecursiveIntersectionControl.decision referenced.domain.key referenced.left referenced.right = .rightReference ∧
  referenced.right.free ≠ [] ∧
  boundId ∈ SourceRecursiveIntersectionDomain.names entered.1.key ∧
  SourcePreparedSharedRows.read heap boundId = some bound ∧
  SourceCurrentNativeEdgeWriterGrowth.History after ∧
  (∃ outerHandle captured finished fuel,
    after.native.nodes.cells outerHandle = some ⟨outer,.returned result⟩ ∧
    Trace fuel (.code (compileNode outer)) captured (.code (.pure result)) finished ∧
    SourceCurrentNativeMuBodyOrigins.Body after fuel outer captured result finished) ∧
  (∃ captured finished fuel name resolved childFuel,
    Good captured ∧ NodeReady captured.native.machine referenced ∧
    after.native.nodes.cells 4 = some ⟨referenced,.returned result⟩ ∧
    captured.native.nodes.cells 4 = some ⟨referenced,.evaluating⟩ ∧
    Trace fuel (.code (compileNode referenced)) captured (.code (.pure result)) finished ∧
    referenced.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
    name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
    SourcePreparedSharedRows.read captured.native.machine.heap name = some resolved ∧
    Trace childFuel (.code (requestNode referenced.domain referenced.left resolved))
      captured (.code (.pure result)) finished ∧
    SourceCurrentNativeForwardLineage.Forwarded after
      ⟨referenced.domain,referenced.left,resolved⟩ captured finished result)
private theorem mainWitness : MainClaim := by
  obtain ⟨count,_below,trace,_⟩ := SourceCurrentNativeKeyAdmission.node_done 128 128 checked
    initial_ready.good initial_ready.semantic other bound other_available bound_available other_closed bound_closed
    node_room edge_room domain_room called_done
  obtain ⟨history,_good,_growth,outerHandle,present,captured,finished,fuel,
    _capturedGood,_ready,_owner,bodyTrace,bodyOrigin,_ownerKept,_finish,_first,_last,_retained⟩ :=
    SourceCurrentNativeMuBodyOrigins.request outer count result initial_ready.good initial_history
      (Or.inr (Or.inr mu_branch)) trace
  obtain ⟨before,next,referenceFuel,good,ready,owner,actual,_kept,_finishTrace,_firstGrowth,_lastGrowth,_retained,choices⟩ :=
    SourceCurrentNativeReferenceOrigins.writer history 4 referenced result reference_present (Or.inr right_branch)
  have selected : ∃ name resolved childFuel,
      referenced.right = .reference (.interned name) ∧ referenceFuel = childFuel + 1 ∧
      name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some resolved ∧
      Trace childFuel (.code (requestNode referenced.domain referenced.left resolved)) before (.code (.pure result)) next ∧
      SourceCurrentNativeForwardLineage.Forwarded after ⟨referenced.domain,referenced.left,resolved⟩ before next result := by
    rcases choices with ⟨wrong,_⟩ | ⟨_,right⟩
    · rw [right_branch] at wrong
      cases wrong
    · exact right
  obtain ⟨name,resolved,childFuel,shape,total,member,found,child,forwarded⟩ := selected
  exact ⟨built_done,bound_recursive,bound_closed,other_closed,source_publications,initial_ready.good,
    called_done,result_empty,mu_branch,swap_branch,right_branch,open_reference,scope_present,actual_binding,history,
    ⟨outerHandle,captured,finished,fuel,present,bodyTrace,bodyOrigin⟩,
    ⟨before,next,referenceFuel,name,resolved,childFuel,good,ready,reference_present,owner,actual,
      shape,total,member,found,child,forwarded⟩⟩
private theorem directWitness : SourceRecursiveIntersectionMemo.requestKey 130 directRequest.domain
    directRequest.left directRequest.right = none ∧
    Trace 1 (.code (requestNode directRequest.domain directRequest.left directRequest.right))
      checked (.code (.pure (.empty : Node))) checked ∧
    SourceCurrentNativeForwardLineage.Forwarded checked directRequest checked checked .empty := by
  exact ⟨direct_key,direct_trace,SourceCurrentNativeReferenceOrigins.forwarded initial_history directRequest 1 .empty
    initial_ready.good direct_trace (SourceEqualityNativeDemandMemo.Retained.refl _)⟩

/-- Own source construction derives a checked entered Mu body and its exact open reference writer. -/
theorem entered_reference :
  built = .done root heap ∧
  (∃ entry body depth ordinary, bound = .mu entry body depth ordinary) ∧
  bound.free = [] ∧ other.free = [] ∧
  Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
  SourceCurrentAllocatedNativePhysicalCompletion.Good checked ∧
  called = .done result after ∧ result = .empty ∧
  SourceRecursiveIntersectionControl.decision outer.domain.key outer.left outer.right = .rightMu ∧
  SourceRecursiveIntersectionControl.decision entered.1.key (.reference (.interned boundId)) leaf = .swap ∧
  SourceRecursiveIntersectionControl.decision referenced.domain.key referenced.left referenced.right = .rightReference ∧
  referenced.right.free ≠ [] ∧
  boundId ∈ SourceRecursiveIntersectionDomain.names entered.1.key ∧
  SourcePreparedSharedRows.read heap boundId = some bound ∧
  SourceCurrentNativeEdgeWriterGrowth.History after ∧
  (∃ outerHandle captured finished fuel,
    after.native.nodes.cells outerHandle = some ⟨outer,.returned result⟩ ∧
    Trace fuel (.code (compileNode outer)) captured (.code (.pure result)) finished ∧
    SourceCurrentNativeMuBodyOrigins.Body after fuel outer captured result finished) ∧
  (∃ captured finished fuel name resolved childFuel,
    Good captured ∧ NodeReady captured.native.machine referenced ∧
    after.native.nodes.cells 4 = some ⟨referenced,.returned result⟩ ∧
    captured.native.nodes.cells 4 = some ⟨referenced,.evaluating⟩ ∧
    Trace fuel (.code (compileNode referenced)) captured (.code (.pure result)) finished ∧
    referenced.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
    name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
    SourcePreparedSharedRows.read captured.native.machine.heap name = some resolved ∧
    Trace childFuel (.code (requestNode referenced.domain referenced.left resolved))
      captured (.code (.pure result)) finished ∧
    SourceCurrentNativeForwardLineage.Forwarded after
      ⟨referenced.domain,referenced.left,resolved⟩ captured finished result) := mainWitness

/-- An unsupported ordinary placeholder keeps the actual direct Empty query and allocates no memo cell. -/
theorem direct_placeholder : SourceRecursiveIntersectionMemo.requestKey 130 directRequest.domain
    directRequest.left directRequest.right = none ∧
    Trace 1 (.code (requestNode directRequest.domain directRequest.left directRequest.right))
      checked (.code (.pure (.empty : Node))) checked ∧
    SourceCurrentNativeForwardLineage.Forwarded checked directRequest checked checked .empty := directWitness

end
end MicroCFTA.NativeEnteredReferenceCheck
