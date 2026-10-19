import MicroCFTA.SourceCurrentNativeOriginViewBranches
import MicroCFTA.SourceCurrentNativeOpenRequestResults
import MicroCFTA.MergedFreshOrdinaryExposureOrigins
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

namespace MicroCFTA.NativeOriginViewKernels
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State 194
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
  .node [.mk ("f",.top) plain [.var 0]],.binder false (.node [.mk ("leaf",.top) plain []])])
private def otherPlan : Syntax Symbol Guard := .node [.mk ("f",.top) plain [.node [.mk ("leaf",.top) plain []]]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [muPlan,otherPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities Cache.emptyState
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : Checked :=
  ⟨initial 194 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
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
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 194 history Cache.empty_valid
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
private theorem bound_available : Available heap bound :=
  source_available.children bound (by cbv; exact .head _)
private theorem other_available : Available heap other :=
  source_available.children other (by cbv; exact .tail _ (.head _))
private theorem bound_closed : bound.free = [] := by cbv
private theorem other_closed : other.free = [] := by cbv
private theorem node_room : checked.native.machine.heap.nodes.next < 2 ^ 192 := by cbv
private theorem edge_room : checked.native.machine.heap.edges.next ≤ 2 ^ (192 + 2) := by cbv
private theorem domain_room : checked.native.machine.domains.next +
    2 ^ (checked.native.machine.heap.nodes.next + checked.native.machine.heap.nodes.next * checked.native.machine.heap.nodes.next) <
      2 ^ (192 + 1) := by cbv
private theorem initial_history : SourceCurrentNativeEdgeWriterGrowth.History checked := .initial _ _
private def called := SourceEqualityNativeDemand.execute 128
  (.code (requestNode outer.domain outer.left outer.right)) checked
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := called.state
private theorem called_done : called = .done result after := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases observed : called <;> simp_all only [result,after,SourceEqualityNativeDemand.Outcome.state,Bool.false_eq_true]
private theorem result_exact : result = other := by cbv

private def added := run (makeEdge ("later-physical-edge",.top) plain []) after.native.machine.heap
private def view := added.2
private def selectedRow : EdgeValue Symbol Guard := (nodeEdges result)[0]?.getD
  (.mk ⟨0,⟨("none",.top),[],plain⟩⟩ [])
private def physicalRead := MergedFreshOrdinaryExposure.nodeEdges 8 result view
private theorem physical_read : physicalRead = .done [selectedRow] view := by cbv
private theorem distinct_view : after.native.machine.heap ≠ view := by
  intro same
  have counts := congrArg (fun state : State Symbol Guard => state.edges.next) same
  have unequal : after.native.machine.heap.edges.next ≠ view.edges.next := by
    have bigger : after.native.machine.heap.edges.next < view.edges.next := by cbv
    exact Nat.ne_of_lt bigger
  exact unequal counts

private theorem checked_witness :
    built = .done root heap ∧ Good checked ∧
    called = .done result after ∧ result = other ∧
    after.native.machine.heap ≠ view ∧
    physicalRead = .done [selectedRow] view ∧
    ∃ count,
      Trace count (.code (requestNode outer.domain outer.left outer.right)) checked (.code (.pure result)) after ∧
      SourceCurrentNativeEdgeWriterGrowth.History after ∧ Good after ∧
      InternedConstructorTemplates.Valid view ∧
      Grows after.native.machine.heap view ∧
      MergedFreshOrdinaryGraph.Origin view [result] selectedRow ∧
      ∃ terminal handle,
        SourceCurrentNativeQueryRowOrigins.Route after result outer terminal ∧
        after.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
        SourceCurrentNativeOriginExposure.Writer after handle terminal result := by
  obtain ⟨count,_below,trace,_⟩ := SourceCurrentNativeKeyAdmission.node_done 192 128 checked
    initial_ready.good initial_ready.semantic other bound other_available bound_available other_closed bound_closed node_room edge_room domain_room called_done
  obtain ⟨history,good,_growth,_origin⟩ := SourceCurrentSharedLeafNativeLineage.request outer count result
    initial_ready.good initial_history trace
  have resultAvailable := SourceCurrentNativeOpenRequestResults.node_result count outer checked after result
    initial_ready.good.native trace
  have edge := SourceEqualityRequiredCache.edge ("later-physical-edge",.top) plain [] after.native.machine.heap
    good.heap (fun _ impossible => by cases impossible)
  have viewValid : InternedConstructorTemplates.Valid view := edge.1.ready.semantic.1.normal.facts.coherent.valid
  have origin : MergedFreshOrdinaryGraph.Origin view [result] selectedRow :=
    MergedFreshOrdinaryExposureOrigins.nodeEdges_origins 8 result view edge.1.ready.semantic edge.1.ready.covered
      (edge.1.available result resultAvailable) [selectedRow] view physical_read view (grows_refl _)
      selectedRow List.mem_cons_self
  obtain ⟨_reached,_final,_grow,terminal,handle,route,cell,_notSwap,_notReset,_first,_second,writer,_unfold⟩ :=
    SourceCurrentNativeOriginViewBranches.request outer count result initial_ready.good initial_history trace
      view viewValid selectedRow origin
  exact ⟨built_done,initial_ready.good,called_done,result_exact,distinct_view,physical_read,count,trace,history,good,
    viewValid,edge.1.growth,origin,terminal,handle,route,cell,writer⟩

/-- Actual captured native tables remain at their query return while a later physical read supplies the row origin. -/
theorem separate_view :
    built = .done root heap ∧ Good checked ∧
    called = .done result after ∧ result = other ∧
    after.native.machine.heap ≠ view ∧
    physicalRead = .done [selectedRow] view ∧
    ∃ count,
      Trace count (.code (requestNode outer.domain outer.left outer.right)) checked (.code (.pure result)) after ∧
      SourceCurrentNativeEdgeWriterGrowth.History after ∧ Good after ∧
      InternedConstructorTemplates.Valid view ∧
      Grows after.native.machine.heap view ∧
      MergedFreshOrdinaryGraph.Origin view [result] selectedRow ∧
      ∃ terminal handle,
        SourceCurrentNativeQueryRowOrigins.Route after result outer terminal ∧
        after.native.nodes.cells handle = some ⟨terminal,.returned result⟩ ∧
        SourceCurrentNativeOriginExposure.Writer after handle terminal result := checked_witness
end
end MicroCFTA.NativeOriginViewKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeOriginViewKernels.separate_view
#print MicroCFTA.NativeOriginViewKernels.separate_view
#print axioms MicroCFTA.NativeOriginViewKernels.separate_view
