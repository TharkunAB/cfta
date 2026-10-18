import MicroCFTA.SourceCurrentNativeKeyAdmission
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NativeKeyAdmissionCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [],.top⟩
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .binder false (.node [
  .mk ("base",.top) plain [],.mk ("repeat",.top) plain [.var 0]])
private def pair : Syntax Symbol Guard := .node [.mk ("pair",.top) own [leaf,leaf]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [pair]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def firstAllocation := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def first : SourceEqualityConstraintAllocation.Value := match firstAllocation.1 with
  | .ok value => value | _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities firstAllocation.2
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : SourceEqualityNativeDemand.State 66 :=
  ⟨initial 66 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private theorem built_done : built = .done root heap := by cbv
private theorem own_cached : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready checked := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) own_cached (show firstAllocation = (.ok first,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [own,plain] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      one SourceEqualityGuardReadback.empty_cached (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [own,plain] := by
    intro guard member
    simp only [expression,pair,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,false_or,or_self] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 66 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private def recursive : Node := ((children ((children root)[0]?.getD .empty))[0]?).getD .empty
private theorem recursive_shape : ∃ entry body depth ordinary, recursive = .mu entry body depth ordinary := by
  have tag : (match recursive with | .mu .. => true | _ => false) = true := by cbv
  cases found : recursive <;> simp_all only [Bool.false_eq_true]
  exact ⟨_,_,_,_,rfl⟩
private theorem root_closed : root.free = [] := by cbv
private theorem node_room : checked.native.machine.heap.nodes.next < 2 ^ 64 := by cbv
private theorem edge_room : checked.native.machine.heap.edges.next ≤ 2 ^ (64 + 2) := by cbv
private theorem domain_room : checked.native.machine.domains.next +
    2 ^ (checked.native.machine.heap.nodes.next + checked.native.machine.heap.nodes.next * checked.native.machine.heap.nodes.next) <
      2 ^ (64 + 1) := by cbv
private def called := SourceEqualityNativeDemand.execute 4
  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain root root)) checked
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := called.state
private theorem called_done : called = .done result after := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases observed : called <;> simp_all only [result,after,SourceEqualityNativeDemand.Outcome.state,Bool.false_eq_true]
private theorem nonzero : checked.native.machine.heap.nodes.next > 0 := by cbv
private theorem witness :
    built = .done root heap ∧
    (∃ entry body depth ordinary, recursive = .mu entry body depth ordinary) ∧
    checked.native.machine.heap.nodes.next > 0 ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good checked ∧
    called = .done result after ∧
    ∃ count, count < 4 ∧ SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace count
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain root root))
        checked (.code (.pure result)) after ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧ Available after.native.machine.heap result ∧
      InternedValueMassHeap.Stored
        (SourceCurrentAllocatedRecursiveMassTrace.massAfter count (InternedValueMassHeap.initialBound heap)) after.native.machine.heap ∧
      InternedValueMass.value result ≤
        SourceCurrentAllocatedRecursiveMassTrace.massAfter count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.nodes.next ≤ checked.native.machine.heap.nodes.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.edges.next ≤ checked.native.machine.heap.edges.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.domains.next ≤ checked.native.machine.domains.next + count := by
  refine ⟨built_done,recursive_shape,nonzero,initial_ready.good,called_done,?_⟩
  exact SourceCurrentNativeKeyAdmission.node_done 64 4 checked initial_ready.good initial_ready.semantic
    root root source_available source_available root_closed root_closed node_room edge_room domain_room called_done

/-- Initial source facts and headroom derive a checked trace for a closed query over a used recursive Mu source. -/
theorem recursive_source :
    built = .done root heap ∧
    (∃ entry body depth ordinary, recursive = .mu entry body depth ordinary) ∧
    checked.native.machine.heap.nodes.next > 0 ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good checked ∧
    called = .done result after ∧
    ∃ count, count < 4 ∧ SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace count
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain root root))
        checked (.code (.pure result)) after ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧ Available after.native.machine.heap result ∧
      InternedValueMassHeap.Stored
        (SourceCurrentAllocatedRecursiveMassTrace.massAfter count (InternedValueMassHeap.initialBound heap)) after.native.machine.heap ∧
      InternedValueMass.value result ≤
        SourceCurrentAllocatedRecursiveMassTrace.massAfter count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.nodes.next ≤ checked.native.machine.heap.nodes.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.heap.edges.next ≤ checked.native.machine.heap.edges.next +
        SourceCurrentAllocatedRecursiveMassTrace.credit count (InternedValueMassHeap.initialBound heap) ∧
      after.native.machine.domains.next ≤ checked.native.machine.domains.next + count := witness

end
end MicroCFTA.NativeKeyAdmissionCheck
