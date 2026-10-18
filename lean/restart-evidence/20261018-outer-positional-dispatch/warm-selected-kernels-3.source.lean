import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentOuterPositionalOrigins
import MicroCFTA.SourceCurrentOuterGuardHeapReturns
import MicroCFTA.SourceCurrentParentProbeHeap
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

namespace MicroCFTA.WarmSelectedKernels
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
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) ownGuard [wide,tau]]
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
  (SourceEqualityClassOrder.recordOf [[0,0,0],[0,0,1]]).getD ⟨.empty,[]⟩
private def records := [record,record]
private def values : List (Value Symbol Guard) := [root]
private def fourth : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private def memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private theorem record_paths : record.paths = [[0,0,0],[0,0,1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0,0],[0,0,1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.branch [(0,.terminal),(1,.terminal)])])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem unselected : SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
  intro path member
  rw [record_paths] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · unfold SourceEqualityEditCompiledPaths.Disjoint
    decide
  · unfold SourceEqualityEditCompiledPaths.Disjoint
    decide
private def raw : Guard := ⟨some [[[0,0,0],[0,0,1]]],.top⟩
private def extra := SourceEqualityConstraintAllocation.construct raw.equalities operations.constraints
private def allocated : SourceEqualityConstraintAllocation.Value := match extra.1 with
  | .ok value => value | _ => .contradiction
private def expandedOperations : SourceEqualityConstraintMemoAllocation.State := {operations with constraints := extra.2}
private def expandedBefore : Checked 16 := ⟨(before 16).native,expandedOperations⟩
private def loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula := ⟨allocated,.top⟩
private def neutral : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula :=
  match SourceEqualityConstraintFieldLookup.load top expandedOperations.constraints with
  | .ok (some value) => value | _ => ⟨.contradiction,.top⟩
private theorem raw_cached : SourceEqualityGuardReadback.Cached raw.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0,0,0],[0,0,1]]] = .normalized [[[0,0,0],[0,0,1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem extra_done : extra = (.ok allocated,extra.2) := by
  apply Prod.ext
  · cbv
  · rfl
private theorem expanded_good : SourceCurrentNativeOperationHeap.Good expandedBefore := by
  have fields := SourceCurrentConjunctionFieldAllocation.construct_field raw operations
    (physical_good 16).operations raw_cached allocated extra.2 extra_done
  exact ⟨(physical_good 16).native,(physical_good 16).heap,fields.1,
    (physical_good 16).fields.grows fields.2.1,(physical_good 16).semantic,(physical_good 16).costs⟩
private theorem loaded_found : SourceEqualityConstraintFieldLookup.load raw expandedBefore.operations.constraints = .ok (some loaded) := by cbv
private theorem neutral_found : SourceEqualityConstraintFieldLookup.load top expandedBefore.operations.constraints = .ok (some neutral) := by cbv
private theorem neutral_ready : SourceEqualityConstraintAllocation.Ready expandedBefore.operations.constraints neutral.stored :=
  (SourceEqualityConstraintFieldLookup.load_ready top expandedBefore.operations.constraints expanded_good.operations.constraints
    SourceEqualityConstraintConstructors.top_cached neutral neutral_found).1
private theorem raw_footprint : ∀ originals : List SourceEqualityClassOrder.Record,
    SourceEqualityPhysicalPayload.own raw = .ok (some originals) → ∀ record ∈ originals,
      SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
  have actual : SourceEqualityPhysicalPayload.own raw = .ok (some [record]) := by cbv
  intro originals read other member
  have same := Option.some.inj (Except.ok.inj (actual.symm.trans read))
  cases same
  cases List.mem_singleton.mp member
  exact unselected

private theorem source_values : InternedNestedProvenance.Values heap values := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  intro value member
  cases List.mem_singleton.mp member
  exact available
private theorem source_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) expression
private theorem source_probes : InternedFreshOrdinaryProbeHeap.Heap heap := by
  simpa only [built,heap] using InternedFreshOrdinaryProbeHeap.closed_heap expression
private def parentSymbol : Symbol := ("parent",.top)
private def initialBuild := SourceCurrentAllocatedMkEdge.build parentSymbol loaded values expandedBefore
private def original : EdgeValue Symbol Guard := match initialBuild.1 with
  | .ok value => value | _ => (run (makeEdge parentSymbol top []) empty).1
private def entryBefore := initialBuild.2
private theorem initial_build : initialBuild = (.ok original,entryBefore) := by
  apply Prod.ext
  · cbv
  · rfl
private theorem initial_effect : SourceCurrentLowerProbeHeap.Effect expandedBefore entryBefore ∧
    InternedEdgeResidency.EdgeResident entryBefore.native.machine.heap original := by
  have loadedReady := SourceEqualityConstraintFieldLookup.load_ready raw expandedBefore.operations.constraints
    expanded_good.operations.constraints raw_cached loaded loaded_found
  exact SourceCurrentParentProbeHeap.build initial_build ⟨expanded_good,source_probes⟩ loadedReady.1
    (by rw [loadedReady.2]; exact ⟨raw_cached,loaded,loaded_found⟩) source_values
private theorem original_children : original.children = values := by cbv
private theorem original_field : original.entry.key.constraint = raw := by cbv
private def caller := SourceCurrentAllocatedPartialState.initial entryBefore memo fourth
private def request : SourceCurrentAllocatedPartialState.EdgeRequest := ⟨neutral.stored,original⟩
private theorem caller_good : SourceCurrentOuterPrefixInvariants.Good caller :=
  SourceCurrentOuterPrefixInvariants.initial entryBefore memo fourth initial_effect.1.good.toGood
    (SourceCurrentMemoMergeEffects.stored_empty _) initial_effect.1.good.probes
private theorem request_ready : SourceCurrentOuterPrefixInvariants.EdgeReady caller request :=
  ⟨neutral_ready.grows initial_effect.1.operations.constraint_growth,initial_effect.2⟩
private theorem entry_guards : SourceCurrentConstrainedCapGuardHeap.Heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) entryBefore.native.machine.heap :=
  SourceCurrentParentGuardHeapReturns.build _ initial_build source_guards
private def cold := SourceCurrentAllocatedPartialWorker.edgeCall 0 4 0 16 12 16 64 16 16 256 0 request caller
private def returned : EdgeValue Symbol Guard := match cold with
  | .done value .. => value | _ => (run (makeEdge parentSymbol top []) empty).1
private def after := cold.state
private theorem cold_done : cold = .done returned after := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases found : cold <;> simp_all only [returned,after,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private def warm := SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 request after
private theorem ready_hit : SourceCurrentAllocatedPartialState.beginEdge request after = (0,.ready returned,after) := by cbv
private theorem warm_done : warm = .done returned after :=
  SourceCurrentAllocatedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0 0 request after after 0 returned ready_hit
private def result : Value Symbol Guard := returned.children[0]?.getD .empty
private theorem output : returned.children[0]? = some result := by
  have tag : returned.children.isEmpty = false := by cbv
  cases found : returned.children with
  | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
  | cons head tail => simp only [result,found,List.getElem?_cons_zero,Option.getD_some]



private theorem positive : ∃ (row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
    row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧
    own ≠ [] ∧ row.children[1]? = some right ∧
    (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
  have tag : (nodeEdges result).isEmpty = false := by cbv
  have own : SourceEqualityPhysicalPayload.own ownGuard = .ok (some
    [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]) := by cbv
  have field : ((nodeEdges result)[0]?).map (fun row => row.entry.key.constraint) = some ownGuard := by cbv
  have second : ((nodeEdges result)[0]?).bind (fun row => row.children[1]?) = some right := by cbv
  have changed : ((nodeEdges result)[0]?).map (fun row => (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf) ≠ some left.referenceOf := by
    cbv
    intro impossible
    cases impossible
  cases found : nodeEdges result with
  | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
  | cons row tail =>
    have rowField : row.entry.key.constraint = ownGuard := Option.some.inj
      (by simpa only [found,List.getElem?_cons_zero,Option.map_some] using field)
    refine ⟨row,[(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩],List.mem_cons_self,?_,by simp,?_,?_⟩
    · rw [rowField]
      exact own
    · simpa only [found,List.getElem?_cons_zero,Option.bind_some] using second
    · intro impossible
      apply changed
      simpa only [found,List.getElem?_cons_zero,Option.map_some] using congrArg some impossible

private theorem witness :
    built = .done root heap ∧ initialBuild = (.ok original,entryBefore) ∧ original.children = values ∧
    cold = .done returned after ∧ warm = .done returned after ∧
    SourceCurrentAllocatedPartialState.beginEdge request after = (0,.ready returned,after) ∧
    SourceCurrentOuterPositionalOrigins.Origins caller ∧ SourceCurrentOuterPositionalOrigins.Origins after ∧
    SourceCurrentOuterPositionalOrigins.EdgeLink original returned ∧ returned.children[0]? = some result ∧
    ∃ (sourceIndex : Nat) (sourceRow row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some sourceRow ∧ row ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin sourceRow row ∧ row.children[1]? = sourceRow.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
  have initialOrigins : SourceCurrentOuterPositionalOrigins.Origins caller :=
    SourceCurrentOuterPositionalOrigins.initial entryBefore memo fourth
  have coldOrigins := SourceCurrentOuterPositionalOrigins.edge_call cold_done caller_good request_ready entry_guards initialOrigins
  have physical := SourceCurrentOuterPrefixInvariants.edge_done cold_done caller_good request_ready
  have ready : SourceCurrentOuterPrefixInvariants.EdgeReady after request :=
    ⟨request_ready.1.grows physical.2.1.operations.constraint_growth,
      InternedEdgeResidency.edge_grows _ _ physical.2.1.keeps.growth _ request_ready.2⟩
  have guards := SourceCurrentOuterGuardHeapReturns.edge_done
    (fun guard : Guard => SourceMemoGate.plain guard = true) cold_done caller_good request_ready entry_guards
  have warmOrigins := SourceCurrentOuterPositionalOrigins.edge_call warm_done physical.1 ready guards coldOrigins.1
  have footprint : ∀ originals : List SourceEqualityClassOrder.Record,
      SourceEqualityPhysicalPayload.own original.entry.key.constraint = .ok (some originals) →
      ∀ record ∈ originals, SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
    rw [original_field]
    exact raw_footprint
  have link := warmOrigins.2 0 1 footprint root result (by change original.children[0]? = some root; rw [original_children]; rfl) output
  obtain ⟨row,own,member,ownRead,nonempty,second,changed⟩ := positive
  obtain ⟨index,sourceRow,input,fields,unchanged⟩ := link.positive member ownRead nonempty
  exact ⟨constructed,initial_build,original_children,cold_done,warm_done,ready_hit,initialOrigins,
    warmOrigins.1,warmOrigins.2,output,index,sourceRow,row,own,input,member,ownRead,nonempty,
    fields,unchanged,second,changed⟩

/-- A cold outer edge call and its zero-fuel ready hit retain one exact positive row origin. -/
theorem cold_then_zero_fuel_warm :
    built = .done root heap ∧ initialBuild = (.ok original,entryBefore) ∧ original.children = values ∧
    cold = .done returned after ∧ warm = .done returned after ∧
    SourceCurrentAllocatedPartialState.beginEdge request after = (0,.ready returned,after) ∧
    SourceCurrentOuterPositionalOrigins.Origins caller ∧ SourceCurrentOuterPositionalOrigins.Origins after ∧
    SourceCurrentOuterPositionalOrigins.EdgeLink original returned ∧ returned.children[0]? = some result ∧
    ∃ (sourceIndex : Nat) (sourceRow row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some sourceRow ∧ row ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin sourceRow row ∧ row.children[1]? = sourceRow.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := witness

end MicroCFTA.WarmSelectedKernels
