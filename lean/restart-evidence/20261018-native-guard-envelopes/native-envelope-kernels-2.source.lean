import MicroCFTA.SourceCurrentNativeGuardEnvelope
import MicroCFTA.SourceCurrentGuardHeapBounds
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentGeneratedQueryGuardResources
import MicroCFTA.SourceCurrentNativeAdmissionWriter
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NativeEnvelopeKernels
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
private def leftMu : Syntax Symbol Guard := .binder false (.node [
  .mk ("base",.top) plain [],.mk ("repeat",.top) plain [.var 0]])
private def rightMu : Syntax Symbol Guard := .binder false (.node [
  .mk ("base",.top) plain [],.mk ("right",.top) plain []])
private def leftPlan : Syntax Symbol Guard := .node [.mk ("pair",.top) plain [leftMu]]
private def rightPlan : Syntax Symbol Guard := .node [.mk ("pair",.top) plain [rightMu]]
private def expression : Syntax Symbol Guard := .node [.mk ("root",.top) plain [leftPlan,rightPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def firstAllocation := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def first : SourceEqualityConstraintAllocation.Value := match firstAllocation.1 with
  | .ok value => value | _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities firstAllocation.2
private def inherited : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def checked : SourceEqualityNativeDemand.State 130 :=
  ⟨initial 130 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
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
    have same : guard = plain := by
      simpa only [expression,leftPlan,rightPlan,leftMu,rightMu,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,false_or,or_self] using member
    cases same
    simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 130 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def leftRecursive : Node := (children left)[0]?.getD .empty
private def rightRecursive : Node := (children right)[0]?.getD .empty
private theorem left_available : Available heap left :=
  source_available.children left (by cbv; exact .head _)
private theorem right_available : Available heap right :=
  source_available.children right (by cbv; exact .tail _ (.head _))
private theorem left_closed : left.free = [] := by cbv
private theorem right_closed : right.free = [] := by cbv
private theorem distinct : left.referenceOf ≠ right.referenceOf := by cbv; intro impossible; cases impossible
private theorem left_recursive : ∃ entry body depth ordinary, leftRecursive = .mu entry body depth ordinary := by
  have tag : (match leftRecursive with | .mu .. => true | _ => false) = true := by cbv
  cases found : leftRecursive <;> simp_all only [Bool.false_eq_true]
  exact ⟨_,_,_,_,rfl⟩
private theorem right_recursive : ∃ entry body depth ordinary, rightRecursive = .mu entry body depth ordinary := by
  have tag : (match rightRecursive with | .mu .. => true | _ => false) = true := by cbv
  cases found : rightRecursive <;> simp_all only [Bool.false_eq_true]
  exact ⟨_,_,_,_,rfl⟩
private theorem node_room : checked.native.machine.heap.nodes.next < 2 ^ 128 := by cbv
private theorem edge_room : checked.native.machine.heap.edges.next ≤ 2 ^ (128 + 2) := by cbv
private theorem domain_room : checked.native.machine.domains.next +
    2 ^ (checked.native.machine.heap.nodes.next + checked.native.machine.heap.nodes.next * checked.native.machine.heap.nodes.next) <
      2 ^ (128 + 1) := by cbv

private theorem left_recursive_available : Available heap leftRecursive :=
  left_available.children leftRecursive (by cbv; exact List.mem_cons_self)
private theorem right_recursive_available : Available heap rightRecursive :=
  right_available.children rightRecursive (by cbv; exact List.mem_cons_self)
private theorem left_recursive_closed : leftRecursive.free = [] := by cbv
private theorem right_recursive_closed : rightRecursive.free = [] := by cbv
private theorem recursive_distinct : leftRecursive.referenceOf ≠ rightRecursive.referenceOf := by
  cbv
  intro impossible
  cases impossible
private def called := SourceEqualityNativeDemand.execute 128
  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain leftRecursive rightRecursive)) checked
private def result : Node := match called with | .done value _ => value | _ => .empty
private def after := called.state
private theorem called_done : called = .done result after := by
  have tag : (match called with | .done .. => true | _ => false) = true := by cbv
  cases observed : called <;> simp_all only [result,after,SourceEqualityNativeDemand.Outcome.state,Bool.false_eq_true]
private theorem nonempty : result.referenceOf ≠ .empty := by cbv; intro impossible; cases impossible
private theorem captured_cells : after.native.nodes.next > 1 ∧ after.native.edges.next > 0 := by cbv
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def operations := SourceEqualityConstraintMemoAllocation.initial allocation.2
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap initial_ready.good.native.machine.1 leftRecursive rightRecursive
    (SourceRecursiveIntersectionOriginalOutput.closed_original leftRecursive heap initial_ready.good.native.machine.1.coherent
      left_recursive_available left_recursive_closed)
    (SourceRecursiveIntersectionOriginalOutput.closed_original rightRecursive heap initial_ready.good.native.machine.1.coherent
      right_recursive_available right_recursive_closed)
    left_recursive_available right_recursive_available left_recursive_closed right_recursive_closed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap SourceCurrentConstrainedCapCheckedJointClosed.Plain heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    SourceCurrentConstrainedCapCheckedJointClosed.Plain expression
private theorem initial_frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory checked :=
  SourceCurrentConstrainedCapGeneratedQueryResources.Frame.initial formulas solver inventory machine operations initial_ready guards rfl
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next,heap.edges.next,machine.domains.next,InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile checked :=
  ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,InternedValueMassHeap.initial heap initial_ready.good.native.machine.1⟩
private theorem room : SourceCurrentAllocatedNativeResourceForecast.Room 128 profile :=
  ⟨node_room,edge_room,domain_room⟩
private def alphabet := SourceCurrentConjunctionGuardUniverse.guards heap
private def limits := SourceCurrentGuardHeapBounds.limits alphabet
private theorem initial_bounds : SourceEqualityAnnotationHeap.Heap
    (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits) heap :=
  SourceCurrentGuardHeapBounds.initial heap initial_ready.good.native.machine.1

private theorem witness (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧
    (∃ entry body depth ordinary,leftRecursive = .mu entry body depth ordinary) ∧
    (∃ entry body depth ordinary,rightRecursive = .mu entry body depth ordinary) ∧
    Available heap leftRecursive ∧ Available heap rightRecursive ∧
    leftRecursive.free = [] ∧ rightRecursive.free = [] ∧ leftRecursive.referenceOf ≠ rightRecursive.referenceOf ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory checked ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile checked ∧
    SourceCurrentAllocatedNativeResourceForecast.Room 128 profile ∧
    SourceEqualityAnnotationHeap.Heap (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits) heap ∧
    called = .done result after ∧ result.referenceOf ≠ .empty ∧
    after.native.nodes.next > 1 ∧ after.native.edges.next > 0 ∧
    ∃ next fuel,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel
        leftRecursive rightRecursive checked result after EndpointMemoGateTrace.empty ∧
      SourceEqualityAnnotationHeap.Heap
        (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
          (SourceCurrentNativeGuardEnvelope.advance limits
            (SourceCurrentAllocatedNativeComputedBudget.instructionBound profile.nodes profile.edges profile.mass)))
        after.native.machine.heap
 := by
  have frame := initial_frame formulas solver
  obtain ⟨next,fuel,value,current,receipt,bounded⟩ := SourceCurrentNativeGuardEnvelope.complete alphabet limits profile
    formulas solver inventory checked frame initial_fits room leftRecursive rightRecursive
    left_recursive_available right_recursive_available left_recursive_closed right_recursive_closed
    (SourceCurrentConjunctionGuardUniverse.initial heap initial_ready.good.native.machine.1)
    (SourceCurrentGuardHeapBounds.alphabet alphabet) EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  obtain ⟨rfl,rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique 128
    (SourceCurrentAllocatedNativeComputedBudget.instructionBound profile.nodes profile.edges profile.mass + 1)
    _ checked after current result value called_done receipt.done
  exact ⟨built_done,left_recursive,right_recursive,left_recursive_available,right_recursive_available,
    left_recursive_closed,right_recursive_closed,recursive_distinct,frame,initial_fits,room,initial_bounds,
    called_done,nonempty,captured_cells.1,captured_cells.2,next,fuel,receipt,bounded⟩

/-- Distinct resident recursive operands retain a computed raw guard envelope through actual native work. -/
theorem distinct_recursive_query (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    built = .done root heap ∧
    (∃ entry body depth ordinary,leftRecursive = .mu entry body depth ordinary) ∧
    (∃ entry body depth ordinary,rightRecursive = .mu entry body depth ordinary) ∧
    Available heap leftRecursive ∧ Available heap rightRecursive ∧
    leftRecursive.free = [] ∧ rightRecursive.free = [] ∧ leftRecursive.referenceOf ≠ rightRecursive.referenceOf ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory checked ∧
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile checked ∧
    SourceCurrentAllocatedNativeResourceForecast.Room 128 profile ∧
    SourceEqualityAnnotationHeap.Heap (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limits) heap ∧
    called = .done result after ∧ result.referenceOf ≠ .empty ∧
    after.native.nodes.next > 1 ∧ after.native.edges.next > 0 ∧
    ∃ next fuel,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel
        leftRecursive rightRecursive checked result after EndpointMemoGateTrace.empty ∧
      SourceEqualityAnnotationHeap.Heap
        (SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
          (SourceCurrentNativeGuardEnvelope.advance limits
            (SourceCurrentAllocatedNativeComputedBudget.instructionBound profile.nodes profile.edges profile.mass)))
        after.native.machine.heap
 := witness formulas solver

end
end MicroCFTA.NativeEnvelopeKernels
