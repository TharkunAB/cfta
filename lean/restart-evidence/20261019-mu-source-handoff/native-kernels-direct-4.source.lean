import MicroCFTA.SourceCurrentNativeOriginBranches
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

namespace MicroCFTA.NativeOriginBranchesKernels
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State 514
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
  .node [.mk ("leaf",.top) plain []],.node [.mk ("f",.top) plain [.var 0]],
  .binder false (.node [.mk ("g",.top) plain [.var 0]])])
private def otherPlan : Syntax Symbol Guard := .node [.mk ("f",.top) plain [.node [.mk ("leaf",.top) plain []]]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [muPlan,otherPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities Cache.emptyState
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : Checked :=
  ⟨initial 514 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
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
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 514 history Cache.empty_valid
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
private theorem node_room : checked.native.machine.heap.nodes.next < 2 ^ 512 := by cbv
private theorem edge_room : checked.native.machine.heap.edges.next ≤ 2 ^ (512 + 2) := by cbv
private theorem domain_room : checked.native.machine.domains.next +
    2 ^ (checked.native.machine.heap.nodes.next + checked.native.machine.heap.nodes.next * checked.native.machine.heap.nodes.next) <
      2 ^ (512 + 1) := by cbv
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
private def referenceHandle : Nat := match SourceRecursiveIntersectionMemo.requestKey 514 referenced.domain referenced.left referenced.right with
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

private def body : Node := match bound with | .mu _ body _ _ => body | _ => .empty
private def unionRequest : NodeRequest Symbol Guard := ⟨entered.1,other,body⟩
private def unionHandle : Nat := match SourceRecursiveIntersectionMemo.requestKey 514 unionRequest.domain
    unionRequest.left unionRequest.right with
  | none => 0
  | some key => (after.native.nodes.table key).getD 0
private theorem union_branch : SourceRecursiveIntersectionControl.decision unionRequest.domain.key
    unionRequest.left unionRequest.right = .rightUnion := by cbv
private theorem union_present : after.native.nodes.cells unionHandle = some ⟨unionRequest,.returned other⟩ := by cbv
private theorem union_open : unionRequest.right.free ≠ [] := by cbv; intro impossible; cases impossible
private def unionRow : EdgeValue Symbol Guard := (nodeEdges other)[0]?.getD
  (.mk ⟨0,⟨("none",.top),[],plain⟩⟩ [])
private theorem union_row : (nodeEdges other)[0]? = some unionRow := by cbv

private theorem union_origin : MergedFreshOrdinaryGraph.Origin after.native.machine.heap [other] unionRow := by
  have shape : ∃ entry rows depth free, other = .node entry rows depth free := by
    have tag : (match other with | .node .. => true | _ => false) = true := by cbv
    cases found : other <;> simp_all only [Bool.false_eq_true]
    exact ⟨_,_,_,_,rfl⟩
  obtain ⟨entry,rows,depth,free,shape⟩ := shape
  rw [shape]
  apply (MergedFreshOrdinaryGraph.origin_node after.native.machine.heap entry rows depth free unionRow).mpr
  have found := union_row
  rw [shape] at found
  exact List.mem_of_getElem? found

private theorem reference_origin : MergedFreshOrdinaryGraph.Origin after.native.machine.heap [leaf] selectedRow := by
  have shape : ∃ entry rows depth free, leaf = .node entry rows depth free := by
    have tag : (match leaf with | .node .. => true | _ => false) = true := by cbv
    cases found : leaf <;> simp_all only [Bool.false_eq_true]
    exact ⟨_,_,_,_,rfl⟩
  obtain ⟨entry,rows,depth,free,shape⟩ := shape
  rw [shape]
  apply (MergedFreshOrdinaryGraph.origin_node after.native.machine.heap entry rows depth free selectedRow).mpr
  have found := selected_row
  rw [shape] at found
  exact List.mem_of_getElem? found

private theorem union_key_safe : SourceRecursiveIntersectionMemo.KeySafe 514 unionRequest.domain
    unionRequest.left unionRequest.right := by
  refine ⟨by decide,?_,.node otherId,.union ((SourceRecursiveIntersectionControl.identity body).getD 0),?_,?_,?_,?_⟩ <;> cbv
private theorem reference_key_safe : SourceRecursiveIntersectionMemo.KeySafe 514 referenced.domain
    referenced.left referenced.right := by
  refine ⟨by decide,?_,.node ((SourceRecursiveIntersectionControl.identity leaf).getD 0),.ref boundId,?_,?_,?_,?_⟩ <;> cbv

private theorem union_warm_trace (good : Good after) :
    Trace 1 (.code (requestNode unionRequest.domain unionRequest.left unionRequest.right))
      after (.code (.pure other)) after := by
  apply SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.cons _ _ _ _ _ _ 0 ?_ ?_ (.refl _ _)
  · exact ⟨(good.native.nodes.checked unionHandle _ union_present).1,fun _ _ => union_key_safe⟩
  · cbv
private theorem reference_warm_trace (good : Good after) :
    Trace 1 (.code (requestNode referenced.domain referenced.left referenced.right))
      after (.code (.pure leaf)) after := by
  apply SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace.cons _ _ _ _ _ _ 0 ?_ ?_ (.refl _ _)
  · exact ⟨(good.native.nodes.checked referenceHandle _ reference_present).1,fun _ _ => reference_key_safe⟩
  · cbv

private theorem checked_witness :
  built = .done root heap ∧ Good checked ∧
  called = .done result after ∧ result = other ∧
  SourceCurrentNativeEdgeWriterGrowth.History after ∧ Good after ∧
  unionRequest.right.free ≠ [] ∧ referenced.right.free ≠ [] ∧
  after.native.nodes.cells unionHandle = some ⟨unionRequest,.returned other⟩ ∧
  after.native.nodes.cells referenceHandle = some ⟨referenced,.returned leaf⟩ ∧
  Trace 1 (.code (requestNode unionRequest.domain unionRequest.left unionRequest.right)) after (.code (.pure other)) after ∧
  Trace 1 (.code (requestNode referenced.domain referenced.left referenced.right)) after (.code (.pure leaf)) after ∧
  (∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List Node) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (index : Nat) (member value : Node) (current next : Checked) (count : Nat),
    unionRequest.right = .union entry members depth free ∧ members[index]? = some member ∧
    InternedValueMass.value member < InternedValueMass.value unionRequest.right ∧
    SourceCurrentNativeOriginBranches.Call after ⟨unionRequest.domain,unionRequest.left,member⟩
      current next count value unionRow) ∧
  (∃ captured finished fuel name resolved childFuel,
    Good captured ∧ NodeReady captured.native.machine referenced ∧
    Trace fuel (.code (compileNode referenced)) captured (.code (.pure leaf)) finished ∧
    referenced.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
    name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
    SourcePreparedSharedRows.read captured.native.machine.heap name = some resolved ∧
    SourceCurrentNativeOriginBranches.Call after ⟨referenced.domain,referenced.left,resolved⟩
      captured finished childFuel leaf selectedRow) := by
  obtain ⟨count,_below,trace,_⟩ := SourceCurrentNativeKeyAdmission.node_done 512 128 checked
    initial_ready.good initial_ready.semantic other bound other_available bound_available other_closed bound_closed
    node_room edge_room domain_room called_done
  obtain ⟨history,good,_growth,_origin⟩ := SourceCurrentSharedLeafNativeLineage.request outer count result
    initial_ready.good initial_history trace
  obtain ⟨entry,members,depth,free,shape,before,next,fuel,_valid,_ready,_owner,_actual,_kept,_finish,
    _first,_last,_retained,values,middle,walkFuel,_walk,index,member,value,current,last,prefixFuel,childFuel,
    suffixFuel,memberFound,_valueFound,small,_total,_prefix,child,_suffix⟩ :=
      SourceCurrentNativeOriginBranches.union history unionHandle unionRequest other union_present false union_branch
        unionRow union_origin
  obtain ⟨captured,finished,fuel,capturedGood,ready,_owner,actual,_kept,_finish,_first,_last,_retained,
    name,resolved,childFuel,refShape,total,scopedName,read,called⟩ :=
      SourceCurrentNativeOriginBranches.reference history referenceHandle referenced leaf reference_present false
        right_branch selectedRow reference_origin
  exact ⟨built_done,initial_ready.good,called_done,result_exact,history,good,union_open,open_reference,
    union_present,reference_present,union_warm_trace good,reference_warm_trace good,
    ⟨entry,members,depth,free,index,member,value,current,last,_,shape,memberFound,small,child⟩,
    captured,finished,fuel,name,resolved,childFuel,capturedGood,ready,actual,refShape,total,scopedName,read,called⟩

/-- A source-built Mu query supplies open union and reference writers, followed by literal warm hits. -/
theorem actual_open_branches :
  built = .done root heap ∧ Good checked ∧
  called = .done result after ∧ result = other ∧
  SourceCurrentNativeEdgeWriterGrowth.History after ∧ Good after ∧
  unionRequest.right.free ≠ [] ∧ referenced.right.free ≠ [] ∧
  after.native.nodes.cells unionHandle = some ⟨unionRequest,.returned other⟩ ∧
  after.native.nodes.cells referenceHandle = some ⟨referenced,.returned leaf⟩ ∧
  Trace 1 (.code (requestNode unionRequest.domain unionRequest.left unionRequest.right)) after (.code (.pure other)) after ∧
  Trace 1 (.code (requestNode referenced.domain referenced.left referenced.right)) after (.code (.pure leaf)) after ∧
  (∃ (entry : Interned InternedBinderProtocol.NodeKey) (members : List Node) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (index : Nat) (member value : Node) (current next : Checked) (count : Nat),
    unionRequest.right = .union entry members depth free ∧ members[index]? = some member ∧
    InternedValueMass.value member < InternedValueMass.value unionRequest.right ∧
    SourceCurrentNativeOriginBranches.Call after ⟨unionRequest.domain,unionRequest.left,member⟩
      current next count value unionRow) ∧
  (∃ captured finished fuel name resolved childFuel,
    Good captured ∧ NodeReady captured.native.machine referenced ∧
    Trace fuel (.code (compileNode referenced)) captured (.code (.pure leaf)) finished ∧
    referenced.right = .reference (.interned name) ∧ fuel = childFuel + 1 ∧
    name ∈ SourceRecursiveIntersectionDomain.names referenced.domain.key ∧
    SourcePreparedSharedRows.read captured.native.machine.heap name = some resolved ∧
    SourceCurrentNativeOriginBranches.Call after ⟨referenced.domain,referenced.left,resolved⟩
      captured finished childFuel leaf selectedRow) := checked_witness

end
end MicroCFTA.NativeOriginBranchesKernels

