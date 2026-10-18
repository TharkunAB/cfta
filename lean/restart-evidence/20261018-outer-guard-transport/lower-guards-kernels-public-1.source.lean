import MicroCFTA.SourceCurrentLowerGuardHeapReturns
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.LowerGuardReturnKernels
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

private def top : Guard := SourceEqualityConstraintConstructors.top
private def tau : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0]])
private def wide : Syntax Symbol Guard := .binder false (.node [
  .mk ("leaf",.top) top [], .mk ("pair",.top) top [.var 0,.var 0], .mk ("extra",.top) top []])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [tau,wide]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def left : Value Symbol Guard := ((children root)[0]?).getD .empty
private def right : Value Symbol Guard := ((children root)[1]?).getD .empty
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
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = top) expression
      (by simp [expression,tau,wide,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed, SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built, heap] using checked
  have loaded := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula) preparedOperations
    prepared_valid
  refine ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine
    ⟨semantic.ready.semantic.1.normal.facts, Cache.empty_valid⟩, semantic.ready, loaded.1, ?_⟩
  intro key row found
  have same := guarded key row found
  rw [same]
  exact loaded.2.2

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
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty, []⟩
private def originalValues : List (Value Symbol Guard) := [left,right]
private def currentMemo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private def edited := SourceCurrentAllocatedClassWorker.pass 8 16 32 16 16 256 [record] originalValues (before 16) currentMemo
private def editedValues : List (Value Symbol Guard) := match edited with | .done values _ _ => values | _ => []
private def editedState := edited.state
private def editedMemo := edited.memo
private theorem edited_done : edited = .done editedValues editedState editedMemo := by
  have tag : (match edited with | .done .. => true | _ => false) = true := by cbv
  cases found : edited <;> simp_all only [editedValues,editedState,editedMemo,
    SourceCurrentAllocatedClassWorker.Outcome.state,SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]

private theorem witness (annotation : Guard → Prop) :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧ left ≠ right ∧
    edited = .done editedValues editedState editedMemo ∧ editedValues.length = 2 ∧
    editedValues.all (fun value => match value with | .mu .. => true | _ => false) = true ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation heap ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation editedState.native.machine.heap ∧
    0 < editedState.native.nodes.next := by
  have initial : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
  have available : InternedNestedProvenance.Values heap originalValues := by
    intro value member
    simp only [originalValues,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact originals.1
    · exact originals.2
  have retained := SourceCurrentLowerGuardHeapReturns.class_pass annotation edited_done
    (physical_good 16) (SourceCurrentMemoMergeEffects.stored_empty heap) available initial
  refine ⟨constructed,?_,?_,edited_done,?_,?_,initial,retained,?_⟩
  · cbv
  · intro same
    have clash := congrArg Value.referenceOf same
    cbv at clash
    cases clash
  · cbv
  · cbv
  · cbv

/-- An actual nonempty class edit retains every predicate's causal guard observations. -/
theorem recursive_class_pass (annotation : Guard → Prop) :
    built = .done root heap ∧ record.paths = [[0],[1]] ∧ left ≠ right ∧
    edited = .done editedValues editedState editedMemo ∧ editedValues.length = 2 ∧
    editedValues.all (fun value => match value with | .mu .. => true | _ => false) = true ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation heap ∧
    SourceCurrentConstrainedCapGuardHeap.Heap annotation editedState.native.machine.heap ∧
    0 < editedState.native.nodes.next := witness annotation

end MicroCFTA.LowerGuardReturnKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.LowerGuardReturnKernels.recursive_class_pass
#print MicroCFTA.LowerGuardReturnKernels.recursive_class_pass
#print axioms MicroCFTA.LowerGuardReturnKernels.recursive_class_pass
