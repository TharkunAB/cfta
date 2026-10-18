import MicroCFTA.SourceCurrentNativeOpenQueryForwarding
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

namespace MicroCFTA.NativeOpenRowCheck
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
private def muPlan : Syntax Symbol Guard := .binder false (.union [
  .node [.mk ("leaf",.top) plain []],.node [.mk ("f",.top) plain [.var 0]]])
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
private theorem result_exact : result = other := by cbv
private def referenceHandle : Nat := match SourceRecursiveIntersectionMemo.requestKey 130 referenced.domain referenced.left referenced.right with
  | none => 0
  | some key => (after.native.nodes.table key).getD 0
private theorem mu_branch : SourceRecursiveIntersectionControl.decision outer.domain.key outer.left outer.right = .rightMu := by cbv
private theorem right_branch : SourceRecursiveIntersectionControl.decision referenced.domain.key referenced.left referenced.right = .rightReference := by cbv
private theorem swap_branch : SourceRecursiveIntersectionControl.decision entered.1.key (.reference (.interned boundId)) leaf = .swap := by cbv
private theorem reference_present : after.native.nodes.cells referenceHandle = some ⟨referenced,.returned leaf⟩ := by cbv
private theorem actual_binding : SourcePreparedSharedRows.read heap boundId = some bound := by cbv
private theorem scope_present : boundId ∈ SourceRecursiveIntersectionDomain.names entered.1.key := by cbv; exact .head _
private theorem open_reference : referenced.right.free ≠ [] := by cbv; intro impossible; cases impossible
private def selectedRow : EdgeValue Symbol Guard := (nodeEdges leaf)[0]?.getD
  (.mk ⟨0,⟨("none",.top),[],plain⟩⟩ [])
private theorem selected_row : (nodeEdges leaf)[0]? = some selectedRow := by cbv
private theorem positive_row : selectedRow.entry.key.symbol = ("leaf",.top) ∧
    selectedRow.children = [] ∧ leaf.referenceOf ≠ .empty := by
  constructor
  · cbv
  constructor
  · cbv
  · cbv; intro impossible; cases impossible

private def swapped : NodeRequest Symbol Guard := ⟨entered.1,.reference (.interned boundId),leaf⟩
private def swappedHandle : Nat := match SourceRecursiveIntersectionMemo.requestKey 130 swapped.domain swapped.left swapped.right with
  | none => 0
  | some key => (after.native.nodes.table key).getD 0
private theorem swapped_present : after.native.nodes.cells swappedHandle = some ⟨swapped,.returned leaf⟩ := by cbv
private theorem swapped_open : swapped.left.free ≠ [] := by cbv; intro impossible; cases impossible
private theorem left_codec : ∃ input, IntersectionFlatMemoKey.input swapped.left.referenceOf = some input :=
  ⟨.ref boundId,rfl⟩
private theorem right_codec : ∃ input, IntersectionFlatMemoKey.input swapped.right.referenceOf = some input := by
  exact ⟨.node ((SourceRecursiveIntersectionControl.identity leaf).getD 0),by cbv⟩

private def CoreClaim : Prop :=
  built = .done root heap ∧
  (∃ entry body depth ordinary, bound = .mu entry body depth ordinary) ∧
  bound.free = [] ∧ other.free = [] ∧
  SourceCurrentAllocatedNativePhysicalCompletion.Good checked ∧
  Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
  called = .done result after ∧ result = other ∧
  selectedRow.entry.key.symbol = ("leaf",.top) ∧ selectedRow.children = [] ∧ leaf.referenceOf ≠ .empty ∧
  (nodeEdges leaf)[0]? = some selectedRow ∧
  boundId ∈ SourceRecursiveIntersectionDomain.names entered.1.key ∧
  SourcePreparedSharedRows.read heap boundId = some bound ∧
  SourceRecursiveIntersectionControl.decision entered.1.key (.reference (.interned boundId)) leaf = .swap ∧
  SourceRecursiveIntersectionControl.decision referenced.domain.key referenced.left referenced.right = .rightReference ∧
  swapped.left.free ≠ [] ∧
  SourceCurrentNativeEdgeWriterGrowth.History after ∧ Good after ∧
  Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
  after.native.nodes.cells swappedHandle = some ⟨swapped,.returned leaf⟩ ∧
  after.native.nodes.cells referenceHandle = some ⟨referenced,.returned leaf⟩ ∧
  (∃ terminal handle, SourceCurrentNativeQueryRowOrigins.Route after leaf swapped terminal ∧
    after.native.nodes.cells handle = some ⟨terminal,.returned leaf⟩ ∧
    SourceCurrentNativeWriterReadyRetention.Written (width := 130) handle terminal leaf after.native ∧
    SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .swap ∧
    SourceRecursiveIntersectionControl.decision terminal.domain.key terminal.left terminal.right ≠ .reset ∧
    (∃ input, IntersectionFlatMemoKey.input terminal.left.referenceOf = some input) ∧
    (∃ input, IntersectionFlatMemoKey.input terminal.right.referenceOf = some input)) ∧
  (∃ captured finished fuel name resolved childFuel,
    Good captured ∧ NodeReady captured.native.machine referenced ∧
    captured.native.nodes.cells referenceHandle = some ⟨referenced,.evaluating⟩ ∧
    Trace fuel (.code (compileNode referenced)) captured (.code (.pure leaf)) finished ∧
    referenced.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
    name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
    SourcePreparedSharedRows.read captured.native.machine.heap name = some resolved ∧
    Trace childFuel (.code (requestNode referenced.domain referenced.left resolved))
      captured (.code (.pure leaf)) finished ∧
    SourceCurrentNativeForwardLineage.Forwarded after
      ⟨referenced.domain,referenced.left,resolved⟩ captured finished leaf)
private theorem coreWitness : CoreClaim := by
  obtain ⟨count,_below,trace,_⟩ := SourceCurrentNativeKeyAdmission.node_done 128 128 checked
    initial_ready.good initial_ready.semantic other bound other_available bound_available other_closed bound_closed
    node_room edge_room domain_room called_done
  obtain ⟨history,good,_growth,_origin⟩ := SourceCurrentSharedLeafNativeLineage.request outer count result
    initial_ready.good initial_history trace
  obtain ⟨published⟩ := source_publications
  obtain ⟨_,⟨finalPublications⟩⟩ := SourceCurrentNativePublicationTrace.from_history trace
    initial_ready.good.heap.semantic published
  have normalized := SourceCurrentNativeOpenQueryForwarding.normalize history swapped leaf left_codec right_codec
    ⟨swappedHandle,swapped_present⟩
  obtain ⟨before,next,referenceFuel,capturedGood,ready,owner,actual,_kept,_finishTrace,_firstGrowth,_lastGrowth,_retained,choices⟩ :=
    SourceCurrentNativeReferenceOrigins.writer history referenceHandle referenced leaf reference_present (Or.inr right_branch)
  have selected : ∃ name resolved childFuel,
      referenced.right = .reference (.interned name) ∧ referenceFuel = childFuel + 1 ∧
      name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
      SourcePreparedSharedRows.read before.native.machine.heap name = some resolved ∧
      Trace childFuel (.code (requestNode referenced.domain referenced.left resolved)) before (.code (.pure leaf)) next ∧
      SourceCurrentNativeForwardLineage.Forwarded after ⟨referenced.domain,referenced.left,resolved⟩ before next leaf := by
    rcases choices with ⟨wrong,_⟩ | ⟨_,right⟩
    · rw [right_branch] at wrong
      cases wrong
    · exact right
  obtain ⟨name,resolved,childFuel,shape,total,member,found,child,forwarded⟩ := selected
  exact ⟨built_done,bound_recursive,bound_closed,other_closed,initial_ready.good,source_publications,
    called_done,result_exact,positive_row.1,positive_row.2.1,positive_row.2.2,selected_row,
    scope_present,actual_binding,swap_branch,right_branch,swapped_open,history,good,⟨finalPublications⟩,
    swapped_present,reference_present,normalized,
    ⟨before,next,referenceFuel,name,resolved,childFuel,capturedGood,ready,owner,actual,shape,total,member,found,child,forwarded⟩⟩

end
end MicroCFTA.NativeOpenRowCheck
