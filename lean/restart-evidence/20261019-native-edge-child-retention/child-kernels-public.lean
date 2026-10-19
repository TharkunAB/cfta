import MicroCFTA.SourceCurrentNativeWriterChildRetention
import MicroCFTA.SourceCurrentNativeReferenceOrigins
import MicroCFTA.SourceCurrentNativeOriginExposure
import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceCurrentNativeRowKeyable
import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceEqualityNormalizationReceipt
/-!
# An actual warm edge retains its earlier child return

Source construction derives the initial native support. A cold node query
publishes the edge and its nonempty children. A later edge request is a
warm hit. The selected child retains its actual return into the same reader.
-/
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.NativeChildRetentionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def first : Syntax Symbol Guard := .node [.mk ("pair",.top) top [leaf,leaf]]
private def second : Syntax Symbol Guard := .node [.mk ("pair",.top) own [leaf,leaf]]
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [first,second]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def firstAllocation := SourceEqualityConstraintAllocation.construct top.equalities Cache.emptyState
private def firstValue := match firstAllocation.1 with | .ok value => value | .error _ => .contradiction
private def secondAllocation := SourceEqualityConstraintAllocation.construct own.equalities firstAllocation.2
private def secondValue := match secondAllocation.1 with | .ok value => value | .error _ => .contradiction
private def before : Checked 130 :=
  ⟨initial 130 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial secondAllocation.2⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain left right)
private noncomputable def cold := execute 64 control before
private noncomputable def output : Node := match cold with | .done value _ => value | _ => .empty
private noncomputable def after := cold.state
private noncomputable def row : Row := (nodeEdges output)[0]?.getD (run (makeEdge ("fallback",.top) top []) heap).1
private noncomputable def child : Node := row.children[0]?.getD .empty
private theorem built_done : built = .done root heap := by cbv
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have cached : SourceEqualityGuardReadback.Cached own.equalities := by
    intro classes same
    cases same
    exact SourceEqualityGuardReadback.normalized
      (show EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] by cbv)
  have firstHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [top] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached
      (show firstAllocation = (.ok firstValue,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState secondAllocation.2 [top,own] :=
    SourceEqualityOriginalAllocationHistory.History.construct firstHistory cached
      (show secondAllocation = (.ok secondValue,secondAllocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [top,own] := by
    intro guard member
    simp only [expression,first,second,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 130 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem initial_good : Good before := initial_ready.good
private theorem available : Available heap left ∧ Available heap right := by
  have source := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
  constructor
  · exact source.children left (by cbv; exact .head _)
  · exact source.children right (by cbv; exact .tail _ (.head _))
private theorem cold_done : cold = .done output after := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases actual : cold <;> simp_all only [output,after,Outcome.state,Bool.false_eq_true]
private theorem warm_done : execute 2 control after = .done output after := by cbv
private theorem selected : (nodeEdges output)[0]? = some row := by cbv
private theorem child_selected : row.children[0]? = some child := by cbv
private theorem positive : ¬ Plain row.entry.key.constraint := by cbv
private theorem branch : SourceRecursiveIntersectionControl.decision request.domain.key left right = .ordinary := by cbv

private noncomputable def firstRow : Row := (nodeEdges left)[0]?.getD row
private noncomputable def secondRow : Row := (nodeEdges right)[0]?.getD row
private noncomputable def edgeRequest : EdgeRequest Symbol Guard := ⟨request.domain,firstRow,secondRow⟩
private noncomputable def edgeHandle : Nat :=
  (after.native.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey 130
    edgeRequest.domain edgeRequest.left edgeRequest.right)).getD 0
private theorem edge_present :
    after.native.edges.cells edgeHandle = some ⟨edgeRequest,.returned row⟩ := by cbv
private theorem edge_lookup : lookupEdge 130 edgeRequest after.native = (edgeHandle,after.native) := by cbv
private theorem edge_demand : demandEdge edgeHandle after.native = (.ready row,after.native) := by cbv
private theorem edge_warm : execute 2 (.code (requestEdge edgeRequest.domain edgeRequest.left edgeRequest.right)) after =
    .done row after := by cbv
private theorem survives : Value.empty ∉ row.children := by
  have nonempty : row.children = [child,child] ∧ child ≠ .empty := by
    constructor
    · cbv
    · intro same
      have reference := congrArg Value.referenceOf same
      cbv at reference
      cases reference
  rw [nonempty.1]
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self]
  exact fun same => nonempty.2 same.symm

private theorem checked_witness :
    built = .done root heap ∧ Good before ∧
    cold = .done output after ∧ execute 2 control after = .done output after ∧
    ¬ Plain row.entry.key.constraint ∧ Value.empty ∉ row.children ∧
    row.children[0]? = some child ∧
    after.native.edges.cells edgeHandle = some ⟨edgeRequest,.returned row⟩ ∧
    lookupEdge 130 edgeRequest after.native = (edgeHandle,after.native) ∧
    demandEdge edgeHandle after.native = (.ready row,after.native) ∧
    execute 2 (.code (requestEdge edgeRequest.domain edgeRequest.left edgeRequest.right)) after = .done row after ∧
    History after ∧ Good after ∧
    SourceCurrentNativeEdgeWriterRetention.Written edgeHandle edgeRequest row after.native ∧
    SourceCurrentNativeEdgeWriterGrowth.Written (width := 130) edgeHandle edgeRequest row after.native.machine.heap ∧
    ∃ (leftChild rightChild : Node) (callBefore callAfter : Checked 130) (fuel childHandle : Nat),
      edgeRequest.left.children[0]? = some leftChild ∧ edgeRequest.right.children[0]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap after.native.machine.heap ∧
      Grows callAfter.native.machine.heap after.native.machine.heap ∧
      Trace fuel (.code (requestNode edgeRequest.domain leftChild rightChild)) callBefore (.code (.pure child)) callAfter ∧
      SourceEqualityNativeDemandMemo.Retained callAfter.native after.native ∧
      SourceCurrentNativeForwardLineage.Forwarded after ⟨edgeRequest.domain,leftChild,rightChild⟩ callBefore callAfter child ∧
      after.native.nodes.cells childHandle = some ⟨⟨edgeRequest.domain,leftChild,rightChild⟩,.returned child⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := 130) childHandle
        ⟨edgeRequest.domain,leftChild,rightChild⟩ child after.native := by
  obtain ⟨count,_below,traced,_⟩ := SourceCurrentNativeKeyAdmission.node_done 128 64 before initial_good
    initial_ready.semantic left right available.1 available.2 (by cbv) (by cbv)
    (by cbv) (by cbv) (by cbv) cold_done
  obtain ⟨history,good,_growth,_origin⟩ := SourceCurrentSharedLeafNativeLineage.request request count output
    initial_good (History.initial ⟨heap,Cache.emptyState⟩ before.operations) traced
  have written := SourceCurrentNativeEdgeWriterRetention.edge_writers history edgeHandle edgeRequest row edge_present
  have selectedChild := SourceCurrentNativeWriterChildRetention.returned history written survives 0 child child_selected
  exact ⟨built_done,initial_good,cold_done,warm_done,positive,survives,child_selected,edge_present,edge_lookup,
    edge_demand,edge_warm,history,good,written,written.forget,selectedChild⟩

/-- An actual warm edge cache hit retains its earlier child return and the exact returned child writer. -/
theorem warm_edge_child :
    built = .done root heap ∧ Good before ∧
    cold = .done output after ∧ execute 2 control after = .done output after ∧
    ¬ Plain row.entry.key.constraint ∧ Value.empty ∉ row.children ∧
    row.children[0]? = some child ∧
    after.native.edges.cells edgeHandle = some ⟨edgeRequest,.returned row⟩ ∧
    lookupEdge 130 edgeRequest after.native = (edgeHandle,after.native) ∧
    demandEdge edgeHandle after.native = (.ready row,after.native) ∧
    execute 2 (.code (requestEdge edgeRequest.domain edgeRequest.left edgeRequest.right)) after = .done row after ∧
    History after ∧ Good after ∧
    SourceCurrentNativeEdgeWriterRetention.Written edgeHandle edgeRequest row after.native ∧
    SourceCurrentNativeEdgeWriterGrowth.Written (width := 130) edgeHandle edgeRequest row after.native.machine.heap ∧
    ∃ (leftChild rightChild : Node) (callBefore callAfter : Checked 130) (fuel childHandle : Nat),
      edgeRequest.left.children[0]? = some leftChild ∧ edgeRequest.right.children[0]? = some rightChild ∧
      Good callBefore ∧ Good callAfter ∧
      Grows callBefore.native.machine.heap after.native.machine.heap ∧
      Grows callAfter.native.machine.heap after.native.machine.heap ∧
      Trace fuel (.code (requestNode edgeRequest.domain leftChild rightChild)) callBefore (.code (.pure child)) callAfter ∧
      SourceEqualityNativeDemandMemo.Retained callAfter.native after.native ∧
      SourceCurrentNativeForwardLineage.Forwarded after ⟨edgeRequest.domain,leftChild,rightChild⟩ callBefore callAfter child ∧
      after.native.nodes.cells childHandle = some ⟨⟨edgeRequest.domain,leftChild,rightChild⟩,.returned child⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := 130) childHandle
        ⟨edgeRequest.domain,leftChild,rightChild⟩ child after.native := checked_witness
end MicroCFTA.NativeChildRetentionKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeChildRetentionKernels.warm_edge_child
#print MicroCFTA.NativeChildRetentionKernels.warm_edge_child
#print axioms MicroCFTA.NativeChildRetentionKernels.warm_edge_child
