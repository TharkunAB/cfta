import MicroCFTA.SourceCurrentActualSharedLeafEvents
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.SharedLeafEventsCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
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
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
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
private def checked : SourceEqualityNativeDemand.State 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
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
      List.mem_append,List.mem_cons,List.not_mem_nil,List.append_nil,or_false,or_self] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem checked_good : SourceCurrentNativeOperationHeap.Good checked :=
  ⟨⟨initial_ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    initial_ready.good.heap,initial_ready.good.operations,initial_ready.good.fields,initial_ready.semantic,initial_ready.costs⟩
private theorem source_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def originals : List Node := [root,root]
private def shared := SourceCurrentAllocatedSharedTargetState.initial checked SourceCurrentMemoMergeGraph.empty
private theorem shared_good : SourceCurrentLowerOperationInvariants.SharedGood shared :=
  SourceCurrentLowerOperationInvariants.SharedGood.initial checked_good
    (SourceCurrentMemoMergeEffects.stored_empty _)
private theorem originals_available : InternedNestedProvenance.Values heap originals := by
  intro value member
  simp only [originals,List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  cases member
  exact source_available
private def cold := SourceCurrentAllocatedSharedEditWorker.leaf 8 16 64 16 256 record originals [0] root shared
private def result : Node := match cold with | .done value _ => value | _ => .empty
private def after := cold.state
private theorem cold_done : cold = .done result after := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases observed : cold <;> simp_all only [result,after,SourceCurrentAllocatedSharedEditWorker.Outcome.state,Bool.false_eq_true]
private def warm := SourceCurrentAllocatedSharedEditWorker.leaf 0 0 0 0 2 record originals [0] root after
private theorem warm_done : warm = .done result after := by cbv
private theorem installed : ∃ target, after.targets [0] = some target ∧ target.referenceOf ≠ .empty := by
  refine ⟨(after.targets [0]).getD .empty,?_,?_⟩
  · cbv
  · cbv; intro impossible; cases impossible
private theorem witness :
    built = .done root heap ∧ SourceCurrentLowerOperationInvariants.SharedGood shared ∧
    shared.targets [0] = none ∧ cold = .done result after ∧ warm = .done result after ∧
    (∃ target, after.targets [0] = some target ∧ target.referenceOf ≠ .empty) ∧
    ∃ (target : Node) (middle : SourceCurrentAllocatedSharedTargetState.State 8)
      (last : SourceEqualityNativeDemand.State 8),
      SourceCurrentAllocatedSharedTargetWorker.force 8 16 64 16 256 record originals [0] shared = .done target middle ∧
      SourceEqualityNativeDemand.execute 256
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) middle.checked =
          .done result last ∧ after = SourceCurrentAllocatedSharedTargetState.advance middle last ∧
      after.targets = middle.targets ∧ after.memo = middle.memo ∧
      (∃ count, count < 256 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) middle.checked
          (.code (.pure result)) last) ∧
      SourceCurrentLowerOperationInvariants.SharedGood after ∧
      Available after.checked.native.machine.heap result ∧
      (∃ (targetChecked : SourceEqualityNativeDemand.State 8) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard),
        SourceCurrentAllocatedTargetWorker.target 8 16 64 16 256 originals
          (SourceEqualityClassTarget.operandPaths record.paths [0]) shared.checked shared.memo = .done target targetChecked saved ∧
        middle = SourceCurrentAllocatedSharedTargetState.store shared [0] target targetChecked saved) := by
  obtain ⟨target,middle,last,forced,queried,final,slots,memo,trace⟩ :=
    SourceCurrentActualSharedLeafEvents.leaf cold_done
  have classification := SourceCurrentActualSharedLeafEvents.force forced
  have miss : ∃ (targetChecked : SourceEqualityNativeDemand.State 8) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard),
      SourceCurrentAllocatedTargetWorker.target 8 16 64 16 256 originals
        (SourceEqualityClassTarget.operandPaths record.paths [0]) shared.checked shared.memo = .done target targetChecked saved ∧
      middle = SourceCurrentAllocatedSharedTargetState.store shared [0] target targetChecked saved := by
    rcases classification with ⟨impossible,_⟩ | ⟨_,completed⟩
    · cases impossible
    · exact completed
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,valid,known⟩ :=
    SourceCurrentActualSharedLeafEvents.physical cold_done shared_good originals_available source_available
  exact ⟨built_done,shared_good,rfl,cold_done,warm_done,installed,
    target,middle,last,forced,queried,final,slots,memo,trace,valid,known,miss⟩

/-- A source-built nonempty class force installs a target and its next selected leaf hits both warm tables. -/
theorem cold_then_warm :
    built = .done root heap ∧ SourceCurrentLowerOperationInvariants.SharedGood shared ∧
    shared.targets [0] = none ∧ cold = .done result after ∧ warm = .done result after ∧
    (∃ target, after.targets [0] = some target ∧ target.referenceOf ≠ .empty) ∧
    ∃ (target : Node) (middle : SourceCurrentAllocatedSharedTargetState.State 8)
      (last : SourceEqualityNativeDemand.State 8),
      SourceCurrentAllocatedSharedTargetWorker.force 8 16 64 16 256 record originals [0] shared = .done target middle ∧
      SourceEqualityNativeDemand.execute 256
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) middle.checked =
          .done result last ∧ after = SourceCurrentAllocatedSharedTargetState.advance middle last ∧
      after.targets = middle.targets ∧ after.memo = middle.memo ∧
      (∃ count, count < 256 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) middle.checked
          (.code (.pure result)) last) ∧
      SourceCurrentLowerOperationInvariants.SharedGood after ∧
      Available after.checked.native.machine.heap result ∧
      (∃ (targetChecked : SourceEqualityNativeDemand.State 8) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard),
        SourceCurrentAllocatedTargetWorker.target 8 16 64 16 256 originals
          (SourceEqualityClassTarget.operandPaths record.paths [0]) shared.checked shared.memo = .done target targetChecked saved ∧
        middle = SourceCurrentAllocatedSharedTargetState.store shared [0] target targetChecked saved) := witness

end
end MicroCFTA.SharedLeafEventsCheck

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SharedLeafEventsCheck.cold_then_warm
#print MicroCFTA.SharedLeafEventsCheck.cold_then_warm
#print axioms MicroCFTA.SharedLeafEventsCheck.cold_then_warm
