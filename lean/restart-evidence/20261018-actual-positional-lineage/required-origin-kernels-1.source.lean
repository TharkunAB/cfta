import MicroCFTA.SourceCurrentActualRequiredRowOrigins
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.RequiredOriginKernels
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
private def ownGuard : Guard := ⟨some [[[0],[1]]],.top⟩
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) ownGuard [wide,tau]]
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
private def paths : List (List Int) := [[0,0,0]]
private def prepared := SourceEqualityRequiredExecution.requireAll 16 64 paths [root] heap
private def preparedValues : List (Value Symbol Guard) := match prepared with | .done values _ => values | _ => []
private def preparedHeap := match prepared with
  | .done _ after | .pending _ after | .unresolved _ after | .exhausted _ after => after
private def output := preparedValues[0]?.getD .empty
private theorem prepared_done : prepared = .done preparedValues preparedHeap := by
  have tag : (match prepared with | .done .. => true | _ => false) = true := by cbv
  cases found : prepared <;> simp_all only [preparedValues,preparedHeap,Bool.false_eq_true]

private theorem witness :
    built = .done root heap ∧ children root = [left,right] ∧ left ≠ right ∧
    prepared = .done preparedValues preparedHeap ∧ preparedValues[0]? = some output ∧
    SourceCurrentActualRequiredRowOrigins.Root output ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (records : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges output ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧
      row.children[1]? = original.children[1]? ∧ row.children[1]? = some right ∧
      (row.children[0]?.getD .empty).referenceOf ≠ left.referenceOf := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have causal (annotation : Guard → Prop) : SourceCurrentConstrainedCapGuardHeap.Heap annotation heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
  have resident : InternedNestedProvenance.Values heap [root] := by
    intro value member
    cases List.mem_singleton.mp member
    exact available
  have selected : preparedValues[0]? = some output := by
    have nonempty : preparedValues.isEmpty = false := by cbv
    cases found : preparedValues with
    | nil => simp only [found,List.isEmpty_nil] at nonempty; cases nonempty
    | cons head tail => simp only [output,found,List.getElem?_cons_zero,Option.getD_some]
  have rootShape : SourceCurrentActualRequiredRowOrigins.Root root := by
    have tag : (match root with | .node .. => true | _ => false) = true := by cbv
    cases found : root <;> simp_all only [SourceCurrentActualRequiredRowOrigins.Root,Bool.false_eq_true]
  have origins := SourceCurrentActualRequiredRowOrigins.prepare prepared_done (physical_good 16) resident
    (causal (fun guard => SourceMemoGate.plain guard = true)) 0 1 rfl selected rootShape (by
      intro entries built
      cases built
      intro needed found children same
      cases found
      cases same
      rfl)
  have positive : ∃ (row : EdgeValue Symbol Guard) (records : List SourceEqualityClassOrder.Record),
      row ∈ nodeEdges output ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧
      records ≠ [] ∧ row.children[1]? = some right ∧
      (row.children[0]?.getD .empty).referenceOf ≠ left.referenceOf := by
    have tag : (nodeEdges output).isEmpty = false := by cbv
    have own : SourceEqualityPhysicalPayload.own ownGuard = .ok (some
        [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]) := by cbv
    have field : ((nodeEdges output)[0]?).map (fun row => row.entry.key.constraint) = some ownGuard := by cbv
    have second : ((nodeEdges output)[0]?).bind (fun row => row.children[1]?) = some right := by cbv
    have changed : ((nodeEdges output)[0]?).map (fun row => (row.children[0]?.getD .empty).referenceOf) ≠ some left.referenceOf := by
      cbv
      intro impossible
      cases impossible
    cases found : nodeEdges output with
    | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
    | cons row tail =>
      have rowField : row.entry.key.constraint = ownGuard := by
        exact Option.some.inj (by simpa only [found,List.getElem?_cons_zero,Option.map_some] using field)
      refine ⟨row,_,List.mem_cons_self,?_,by simp,?_,?_⟩
      · rw [rowField]
        exact own
      · simpa only [found,List.getElem?_cons_zero,Option.bind_some] using second
      · intro impossible
        apply changed
        simpa only [found,List.getElem?_cons_zero,Option.map_some] using congrArg some impossible
  obtain ⟨row,records,member,own,nonempty,second,changed⟩ := positive
  obtain ⟨index,original,sourceIndex,fields,unchanged⟩ := origins.2.positive member own nonempty
  refine ⟨constructed,?_,?_,prepared_done,selected,origins.1,index,original,row,records,
    sourceIndex,member,own,nonempty,fields,unchanged,second,changed⟩
  · cbv
  · intro equal
    have clash := congrArg Value.referenceOf equal
    cbv at clash
    cases clash

/-- Initial preparation changes one recursive child and retains a positive full-guard row's other recursive child. -/
theorem positive_required_origin :
    built = .done root heap ∧ children root = [left,right] ∧ left ≠ right ∧
    prepared = .done preparedValues preparedHeap ∧ preparedValues[0]? = some output ∧
    SourceCurrentActualRequiredRowOrigins.Root output ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (records : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges output ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧
      row.children[1]? = original.children[1]? ∧ row.children[1]? = some right ∧
      (row.children[0]?.getD .empty).referenceOf ≠ left.referenceOf := witness

end MicroCFTA.RequiredOriginKernels
