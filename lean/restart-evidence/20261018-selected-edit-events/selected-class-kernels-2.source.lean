import MicroCFTA.SourceCurrentActualLocalRowOrigins
import MicroCFTA.SourceCurrentActualClassDispatch
import MicroCFTA.SourceCurrentActualSharedLeafEvents
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



private theorem active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0],by simp,[1],by simp,by decide⟩
private theorem selected_first : ∃ shared,
    shared.checked = after ∧ shared.memo = saved ∧
    SourceCurrentAllocatedSharedEditWorker.children
      (SourceCurrentAllocatedSharedEditWorker.edit record values 2 4 16 64 16 128)
      [(0,.editAt [0]),(1,.editAt [1])] 1 (values.drop 1) middle = .done (results.drop 1) shared ∧
    [0] ∈ record.paths ∧
    SourceCurrentAllocatedSharedEditWorker.leaf 4 16 64 16 128 record values [0] root initialShared = .done root middle := by
  have selected : results[0]? = some root := by rw [result_values]; rfl
  obtain ⟨entries,shared,start,finish,original,built,checked,memo,input,earlier,later,dispatch⟩ :=
    SourceCurrentActualClassDispatch.class_dispatch class_done coherent active 0 selected
  have sameEntries : entries = [(0,.editAt [0]),(1,.editAt [1])] :=
    SourceEqualityEdits.Edits.editBelow.inj (built.symm.trans compiled_shape)
  subst entries
  have sameOriginal : original = root := Option.some.inj (input.symm.trans rfl)
  subst original
  have sameStart : initialShared = start := by
    have same := congrArg SourceCurrentAllocatedSharedEditWorker.Outcome.state earlier
    simpa only [List.take_zero,SourceCurrentAllocatedSharedEditWorker.children,
      SourceCurrentAllocatedSharedEditWorker.Outcome.state] using same
  subst start
  have found : SourceEqualityNeededMap.lookup (0 : Int) [(0,.editAt [0]),(1,.editAt [1])] = some (.editAt [0]) := rfl
  rcases dispatch with absent | ⟨_lookup,member,_positive,actual⟩ | ⟨entries,lookup,_positive,actual⟩
  · rw [found] at absent
    cases absent.1
  · have sameFinish : finish = middle := by
      have first : SourceCurrentAllocatedSharedEditWorker.leaf 4 16 64 16 128 record values [0] root initialShared = .done root middle :=
        by simpa only [first_value] using first_done
      have same := congrArg SourceCurrentAllocatedSharedEditWorker.Outcome.state (actual.symm.trans first)
      exact same
    subst finish
    exact ⟨shared,checked,memo,later,member,actual⟩
  · rw [found] at lookup
    cases lookup
private def firstForce := SourceCurrentAllocatedSharedTargetWorker.force 4 16 64 16 128 record values [0] initialShared
private def forceAfter := firstForce.state
private theorem force_done : firstForce = .done root forceAfter := by
  have tag : (match firstForce with | .done value _ => some value | _ => none) = some root := by cbv
  cases found : firstForce with
  | failed => simp only [found] at tag; cases tag
  | done value checked =>
    simp only [found] at tag
    cases Option.some.inj tag
    simp only [forceAfter,found,SourceCurrentAllocatedSharedTargetWorker.Outcome.state]
private def positiveRow : EdgeValue Symbol Guard := ((nodeEdges root)[0]?).getD
  ((run (makeEdge ("fallback",.top) top []) empty).1)
private theorem positive_row : positiveRow ∈ nodeEdges root ∧ positiveRow.entry.key.constraint = ownGuard := by
  constructor
  · cbv
    exact List.mem_cons_self
  · cbv

private theorem witness :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧
    SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow [(0,.editAt [0]),(1,.editAt [1])] ∧
    executed = .done results after saved ∧ results = values ∧
    ∃ shared target forced checked targetChecked targetSaved count,
      shared.checked = after ∧ shared.memo = saved ∧
      SourceCurrentAllocatedSharedEditWorker.children
        (SourceCurrentAllocatedSharedEditWorker.edit record values 2 4 16 64 16 128)
        [(0,.editAt [0]),(1,.editAt [1])] 1 (values.drop 1) middle = .done (results.drop 1) shared ∧
      [0] ∈ record.paths ∧
      SourceCurrentAllocatedSharedEditWorker.leaf 4 16 64 16 128 record values [0] root initialShared = .done root middle ∧
      firstForce = .done target forced ∧ target = root ∧ initialShared.targets [0] = none ∧
      SourceCurrentAllocatedTargetWorker.target 4 16 64 16 128 values
        (SourceEqualityClassTarget.operandPaths record.paths [0]) initialShared.checked initialShared.memo =
          .done target targetChecked targetSaved ∧
      forced = SourceCurrentAllocatedSharedTargetState.store initialShared [0] target targetChecked targetSaved ∧
      SourceEqualityNativeDemand.execute 128
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) forced.checked =
          .done root checked ∧ middle = SourceCurrentAllocatedSharedTargetState.advance forced checked ∧
      count < 128 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) forced.checked
        (.code (.pure root)) checked ∧
      SourceCurrentLowerOperationInvariants.SharedGood forced ∧ SourceCurrentLowerOperationInvariants.SharedGood middle ∧
      Available middle.checked.native.machine.heap root ∧
      positiveRow ∈ nodeEdges target ∧ positiveRow.entry.key.constraint = ownGuard ∧
      SourceEqualityPhysicalPayload.own ownGuard = .ok (some [record]) := by
  obtain ⟨shared,sharedChecked,sharedMemo,later,member,actual⟩ := selected_first
  have available : Available heap root := source_values root (by simp [values])
  obtain ⟨target,forced,checked,forcedDone,queried,final,_effect,forcedGood,_known,_inputKnown,_total,finalGood,resultKnown⟩ :=
    SourceCurrentActualSharedLeafEvents.physical actual initial_shared_good source_values available
  have targetSame : target = root :=
    (SourceCurrentAllocatedSharedTargetWorker.Outcome.done.inj (force_done.symm.trans forcedDone)).1.symm
  have targetActual := SourceCurrentActualSharedLeafEvents.force forcedDone
  rcases targetActual with hit | ⟨missing,targetChecked,targetSaved,targetDone,stored⟩
  · have absent : initialShared.targets [0] = none := rfl
    rw [absent] at hit
    cases hit.1
  · obtain ⟨count,bound,steps⟩ := SourceEqualityNativeDemand.done_trace 128 _ _ _ _ queried
    have rowMember : positiveRow ∈ nodeEdges target := by rw [targetSame]; exact positive_row.1
    have ownRead : SourceEqualityPhysicalPayload.own ownGuard = .ok (some [record]) := by cbv
    exact ⟨constructed,record_paths,compiled_shape,class_done,result_values,shared,target,forced,checked,targetChecked,targetSaved,count,
      sharedChecked,sharedMemo,later,member,actual,forcedDone,targetSame,missing,targetDone,stored,queried,final,bound,steps,
      forcedGood,finalGood,resultKnown,rowMember,positive_row.2,ownRead⟩

/-- A selected whole-slot class leaf derives its actual target miss, native steps, and positive target guard. -/
theorem selected_leaf_events :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧
    SourceCurrentAllocatedClassEditPlan.compiled record = .editBelow [(0,.editAt [0]),(1,.editAt [1])] ∧
    executed = .done results after saved ∧ results = values ∧
    ∃ shared target forced checked targetChecked targetSaved count,
      shared.checked = after ∧ shared.memo = saved ∧
      SourceCurrentAllocatedSharedEditWorker.children
        (SourceCurrentAllocatedSharedEditWorker.edit record values 2 4 16 64 16 128)
        [(0,.editAt [0]),(1,.editAt [1])] 1 (values.drop 1) middle = .done (results.drop 1) shared ∧
      [0] ∈ record.paths ∧
      SourceCurrentAllocatedSharedEditWorker.leaf 4 16 64 16 128 record values [0] root initialShared = .done root middle ∧
      firstForce = .done target forced ∧ target = root ∧ initialShared.targets [0] = none ∧
      SourceCurrentAllocatedTargetWorker.target 4 16 64 16 128 values
        (SourceEqualityClassTarget.operandPaths record.paths [0]) initialShared.checked initialShared.memo =
          .done target targetChecked targetSaved ∧
      forced = SourceCurrentAllocatedSharedTargetState.store initialShared [0] target targetChecked targetSaved ∧
      SourceEqualityNativeDemand.execute 128
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) forced.checked =
          .done root checked ∧ middle = SourceCurrentAllocatedSharedTargetState.advance forced checked ∧
      count < 128 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target root)) forced.checked
        (.code (.pure root)) checked ∧
      SourceCurrentLowerOperationInvariants.SharedGood forced ∧ SourceCurrentLowerOperationInvariants.SharedGood middle ∧
      Available middle.checked.native.machine.heap root ∧
      positiveRow ∈ nodeEdges target ∧ positiveRow.entry.key.constraint = ownGuard ∧
      SourceEqualityPhysicalPayload.own ownGuard = .ok (some [record]) := witness

end MicroCFTA.SelectedClassKernels
