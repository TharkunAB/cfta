import MicroCFTA.SourceCurrentActualEditRowOrigins
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.ActualEditRowOriginKernels
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
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) top [wide,tau]]
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
private def shared := SourceCurrentAllocatedSharedTargetState.initial (before 16) currentMemo
private def edits : SourceEqualityEdits.Edits EqualityNormalize.Path := .editBelow [(0,.editAt [0])]
private def edited := SourceCurrentAllocatedSharedEditWorker.edit record originalValues 8 16 32 16 16 256 edits root shared
private def editedValue : Value Symbol Guard := match edited with | .done value _ => value | _ => .empty
private def editedState := edited.state
private theorem edited_done : edited = .done editedValue editedState := by
  have tag : (match edited with | .done .. => true | _ => false) = true := by cbv
  cases found : edited <;> simp_all only [editedValue,editedState,
    SourceCurrentAllocatedSharedEditWorker.Outcome.state,Bool.false_eq_true]
private theorem original_available : InternedNestedProvenance.Values heap originalValues := by
  intro value member
  simp only [originalValues,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact originals.1
  · exact originals.2

private theorem witness :
    built = .done root heap ∧ children root = [left,right] ∧ left ≠ right ∧
    edited = .done editedValue editedState ∧ SourceEqualityRequiredCache.Ordinary editedValue ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges editedValue ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧
      row.children[1]? = original.children[1]? ∧ row.children[1]? = some right ∧
      0 < editedState.checked.native.nodes.next := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have good := SourceCurrentLowerOperationInvariants.SharedGood.initial (physical_good 16)
    (SourceCurrentMemoMergeEffects.stored_empty heap)
  have shape : ∃ entry rows depth free, root = .node entry rows depth free := by
    have tag : (match root with | .node .. => true | _ => false) = true := by cbv
    cases found : root with
    | node entry rows depth free => exact ⟨entry,rows,depth,free,rfl⟩
    | empty | reference | mu | union => simp only [found] at tag; cases tag
  obtain ⟨entry,rows,depth,free,same⟩ := shape
  have actual : SourceCurrentAllocatedSharedEditWorker.edit record originalValues 8 16 32 16 16 256
      (.editBelow [(0,.editAt [0])]) (.node entry rows depth free) shared = .done editedValue editedState := by
    rw [← same]
    exact edited_done
  have rootAvailable : Available heap (.node entry rows depth free) := same ▸ available
  have ordinary := SourceCurrentActualEditRowOrigins.edit_node_ordinary actual good original_available rootAvailable
  have positive : ∃ row, row ∈ nodeEdges editedValue ∧ row.children[1]? = some right := by
    have tag : (nodeEdges editedValue).isEmpty = false := by cbv
    have second : ((nodeEdges editedValue)[0]?).bind (fun row => row.children[1]?) = some right := by cbv
    cases found : nodeEdges editedValue with
    | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
    | cons row tail =>
      refine ⟨row,List.mem_cons_self,?_⟩
      simpa only [found,List.getElem?_cons_zero,Option.bind_some] using second
  obtain ⟨row,selected,secondChild⟩ := positive
  have origin := SourceCurrentActualEditRowOrigins.edit_node actual good original_available rootAvailable 1 rfl selected
  obtain ⟨index,original,present,fields,unchanged⟩ := origin
  refine ⟨constructed,?_,?_,edited_done,ordinary,index,original,row,?_,selected,fields,unchanged,secondChild,?_⟩
  · cbv
  · intro equal
    have clash := congrArg Value.referenceOf equal
    cbv at clash
    cases clash
  · simpa only [same,nodeEdges] using present
  · cbv

/-- An actual recursive native edit retains the ordinary survivor's unselected recursive child. -/
theorem recursive_child_survivor :
    built = .done root heap ∧ children root = [left,right] ∧ left ≠ right ∧
    edited = .done editedValue editedState ∧ SourceEqualityRequiredCache.Ordinary editedValue ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges editedValue ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧
      row.children[1]? = original.children[1]? ∧ row.children[1]? = some right ∧
      0 < editedState.checked.native.nodes.next := witness

end MicroCFTA.ActualEditRowOriginKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.ActualEditRowOriginKernels.recursive_child_survivor
#print MicroCFTA.ActualEditRowOriginKernels.recursive_child_survivor
#print axioms MicroCFTA.ActualEditRowOriginKernels.recursive_child_survivor
