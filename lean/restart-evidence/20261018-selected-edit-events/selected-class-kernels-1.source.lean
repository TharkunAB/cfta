import MicroCFTA.SourceCurrentActualLocalRowOrigins
import MicroCFTA.SourceCurrentActualLocalReduceRowOrigins
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.SelectedClassKernels
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

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

private def top : Guard := SourceEqualityConstraintConstructors.top
private def tau : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0]])
private def wide : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0], .mk ("extra",.top) top []])
private def ownGuard : Guard := ⟨some [[[0],[1]]],.top⟩
private def expression : Syntax Symbol Guard := .node [.mk ("pair",.top) ownGuard [tau,tau]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD (Value.empty : Value Symbol Guard)
private def right : Value Symbol Guard := ((children root)[1]?).getD (Value.empty : Value Symbol Guard)
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def seedEqualities : Option EqualityNormalize.Constraints := some [[[0], [1]]]
private def seedBuild := SourceEqualityConstraintAllocation.construct seedEqualities Cache.emptyState
private def seedValue : SourceEqualityConstraintAllocation.Value := match seedBuild.1 with
  | .ok value => value
  | .error _ => .contradiction
private def seedState := SourceEqualityConstraintMemoAllocation.initial seedBuild.2
private def preparedOperations := (SourceEqualityConstraintMemoAllocation.descend seedValue 0 seedState).2
private def operations := SourceEqualityMkEdgeAllocation.emptyField preparedOperations

private theorem seed_cached : SourceEqualityGuardReadback.Cached seedEqualities := by
  have actual : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized actual

private theorem seed_constructed : seedBuild.1 = .ok seedValue := by cbv

private theorem prepared_valid : SourceEqualityConstraintMemoAllocation.Valid preparedOperations := by
  obtain ⟨value, cache, built, cacheValid, ready, _steps, _read, _classes⟩ :=
    SourceEqualityConstraintAllocation.construct_complete seedEqualities seed_cached Cache.emptyState Cache.empty_valid
  have same : value = seedValue := Except.ok.inj ((congrArg Prod.fst built).symm.trans seed_constructed)
  subst value
  have cacheSame : cache = seedBuild.2 := (congrArg Prod.snd built).symm
  subst cache
  exact (SourceEqualityConstraintMemoAllocation.descend_correct seedValue 0 seedState
    (SourceEqualityConstraintMemoAllocation.initial_valid _ cacheValid) ready).1
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩
private theorem constructed : built = .done root heap := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, InternedNestedConstruction.Outcome.state]

private theorem initial_good (width : Nat) : Good (before width) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top ∨ guard = ownGuard) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top ∨ guard = ownGuard) expression
      (by simp [expression,tau,wide,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) preparedOperations
    prepared_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  rcases guarded key row found with same | same
  · rw [same]
    exact loaded.2.2
  · rw [same]
    refine ⟨seed_cached,⟨⟨seedValue,.top⟩,?_⟩⟩
    cbv

private theorem originals : Available heap left ∧ Available heap right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  constructor
  · exact available.children left (by cbv; exact .head _)
  · exact available.children right (by cbv; exact .tail _ (.head _))


private theorem physical_good (width : Nat) : SourceCurrentNativeOperationHeap.Good (before width) := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have costs : InternedFreshOrdinaryCostHeap.Heap heap := by
    simpa only [built,heap] using InternedFreshOrdinaryCosts.closed_heap expression
  exact SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked (initial_good width)) semantic costs
private instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private def records := [record,record]
private def values : List (Value Symbol Guard) := [root,root]
private def fourth : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private def memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private theorem record_paths : record.paths = [[0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.terminal),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked

private def initialShared := SourceCurrentAllocatedSharedTargetState.initial (before 16) memo
private def executed := SourceCurrentAllocatedClassWorker.runClass 2 4 16 64 16 128 record values (before 16) memo
private def results : List (Value Symbol Guard) := match executed with | .done values .. => values | _ => []
private def after := executed.state
private def saved := executed.memo
private theorem class_done : executed = .done results after saved := by
  have tag : (match executed with | .done .. => true | _ => false) = true := by cbv
  cases found : executed <;> simp_all only [results,after,saved,
    SourceCurrentAllocatedClassWorker.Outcome.state,SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]
private theorem result_values : results = values := by cbv
private theorem compiled_shape : SourceCurrentAllocatedClassEditPlan.compiled record =
    .editBelow [(0,.editAt [0]),(1,.editAt [1])] := by cbv
private theorem source_values : InternedNestedProvenance.Values heap values := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  intro value member
  simp only [values,List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  cases member
  exact available
private theorem initial_shared_good : SourceCurrentLowerOperationInvariants.SharedGood initialShared :=
  SourceCurrentLowerOperationInvariants.SharedGood.initial (physical_good 16)
    (SourceCurrentMemoMergeEffects.stored_empty heap)
private def firstLeaf := SourceCurrentAllocatedSharedEditWorker.leaf 4 16 64 16 128 record values [0] root initialShared
private def firstResult : Value Symbol Guard := match firstLeaf with | .done value .. => value | _ => .empty
private def middle := firstLeaf.state
private theorem first_done : firstLeaf = .done firstResult middle := by
  have tag : (match firstLeaf with | .done .. => true | _ => false) = true := by cbv
  cases found : firstLeaf <;> simp_all only [firstResult,middle,
    SourceCurrentAllocatedSharedEditWorker.Outcome.state,Bool.false_eq_true]
private theorem first_value : firstResult = root := by cbv

end MicroCFTA.SelectedClassKernels
