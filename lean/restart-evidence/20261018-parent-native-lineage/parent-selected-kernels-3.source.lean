import MicroCFTA.SourceCurrentActualLocalRowOrigins
import MicroCFTA.SourceCurrentActualLocalReduceRowOrigins
import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentActualParentRowOrigins
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
set_option linter.all true
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
set_option maxRecDepth 30000

noncomputable section

namespace MicroCFTA.ParentSelectedKernels
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
private def scan := SourceCurrentAllocatedRecordScanWorker.scan 4 0 16 64 256 0 values records (before 16) fourth
private def scanResult : SourceCurrentAllocatedRecordScanWorker.Result := match scan with
  | .done result _ _ => result | _ => (none,[])
private theorem scan_done : scan = .done (none,records) scan.state scan.memo := by
  have tag : (match scan with | .done .. => true | _ => false) = true := by cbv
  have value : scanResult = (none,records) := by cbv
  cases found : scan with
  | failed => simp only [found] at tag; cases tag
  | done result checked saved =>
    simp only [scanResult,found] at value
    cases value
    rfl
private def reduced := SourceCurrentAllocatedLocalWorker.classes 4 0 16 12 16 64 16 16 256 0
  records values (before 16) fourth memo
private def results : List (Value Symbol Guard) := match reduced with | .done values .. => values | _ => []
private def after := reduced.state
private def saved := reduced.fourth
private def current := reduced.memo
private def result := results[0]?.getD (Value.empty : Value Symbol Guard)
private theorem reduced_done : reduced = .done results after saved current := by
  have tag : (match reduced with | .done .. => true | _ => false) = true := by cbv
  cases found : reduced <;> simp_all only [results,after,saved,current,
    SourceCurrentAllocatedLocalWorker.Outcome.state,SourceCurrentAllocatedLocalWorker.Outcome.fourth,
    SourceCurrentAllocatedLocalWorker.Outcome.memo,Bool.false_eq_true]

private theorem witness :
    built = .done root heap ∧ record.paths = [[0,0,0],[0,0,1]] ∧ records.length = 2 ∧
    scan = .done (none,records) scan.state scan.memo ∧
    reduced = .done results after saved current ∧ results[0]? = some result ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have resident : InternedNestedProvenance.Values heap values := by
    intro value member
    cases List.mem_singleton.mp member
    exact available
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) expression
  have coherence : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record := by
    intro other member
    simp only [records,List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    cases member
    exact coherent
  have footprint : ∀ record ∈ records, SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
    intro other member
    simp only [records,List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    cases member
    exact unselected
  have output : results[0]? = some result := by
    have tag : results.isEmpty = false := by cbv
    cases found : results with
    | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
    | cons head tail => simp only [result,found,List.getElem?_cons_zero,Option.getD_some]
  have link := SourceCurrentActualLocalRowOrigins.classes reduced_done (physical_good 16)
    (SourceCurrentMemoMergeEffects.stored_empty heap) resident guards coherence 0 1 footprint rfl output
  have positive : ∃ (row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
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
  obtain ⟨row,own,member,ownRead,nonempty,second,changed⟩ := positive
  obtain ⟨index,original,input,fields,unchanged⟩ := link.positive member ownRead nonempty
  exact ⟨constructed,record_paths,rfl,scan_done,reduced_done,output,index,original,row,own,
    input,member,ownRead,nonempty,fields,unchanged,second,changed⟩

/-- Two actual selected class passes preserve a positive source row and its unselected recursive child. -/
private theorem repeated_local_classes :
    built = .done root heap ∧ record.paths = [[0,0,0],[0,0,1]] ∧ records.length = 2 ∧
    scan = .done (none,records) scan.state scan.memo ∧
    reduced = .done results after saved current ∧ results[0]? = some result ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges result ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := witness

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
private def fullReduced := SourceCurrentAllocatedLocalWorker.reduce 4 0 16 12 16 64 16 16 256 0
  loaded neutral.stored values expandedBefore fourth memo
private def fullResults : List (Value Symbol Guard) := match fullReduced with | .done values .. => values | _ => []
private def fullAfter := fullReduced.state
private def fullSaved := fullReduced.fourth
private def fullCurrent := fullReduced.memo
private def fullResult := fullResults[0]?.getD (Value.empty : Value Symbol Guard)
private theorem full_done : fullReduced = .done fullResults fullAfter fullSaved fullCurrent := by
  have tag : (match fullReduced with | .done .. => true | _ => false) = true := by cbv
  cases found : fullReduced <;> simp_all only [fullResults,fullAfter,fullSaved,fullCurrent,
    SourceCurrentAllocatedLocalWorker.Outcome.state,SourceCurrentAllocatedLocalWorker.Outcome.fourth,
    SourceCurrentAllocatedLocalWorker.Outcome.memo,Bool.false_eq_true]
private theorem full_witness :
    built = .done root heap ∧
    SourceEqualityConstraintFieldLookup.load raw expandedBefore.operations.constraints = .ok (some loaded) ∧
    fullReduced = .done fullResults fullAfter fullSaved fullCurrent ∧ fullResults[0]? = some fullResult ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges fullResult ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have resident : InternedNestedProvenance.Values heap values := by
    intro value member
    cases List.mem_singleton.mp member
    exact available
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) expression
  have output : fullResults[0]? = some fullResult := by
    have tag : fullResults.isEmpty = false := by cbv
    cases found : fullResults with
    | nil => simp only [found,List.isEmpty_nil] at tag; cases tag
    | cons head tail => simp only [fullResult,found,List.getElem?_cons_zero,Option.getD_some]
  have link := SourceCurrentActualLocalReduceRowOrigins.reduce full_done expanded_good
    (SourceCurrentMemoMergeEffects.stored_empty heap) raw raw_cached loaded_found neutral_ready resident guards
    0 1 raw_footprint rfl output
  have positive : ∃ (row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      row ∈ nodeEdges fullResult ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧
      own ≠ [] ∧ row.children[1]? = some right ∧
      (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
    have tag : (nodeEdges fullResult).isEmpty = false := by cbv
    have own : SourceEqualityPhysicalPayload.own ownGuard = .ok (some
      [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]) := by cbv
    have field : ((nodeEdges fullResult)[0]?).map (fun row => row.entry.key.constraint) = some ownGuard := by cbv
    have second : ((nodeEdges fullResult)[0]?).bind (fun row => row.children[1]?) = some right := by cbv
    have changed : ((nodeEdges fullResult)[0]?).map (fun row => (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf) ≠ some left.referenceOf := by
      cbv
      intro impossible
      cases impossible
    cases found : nodeEdges fullResult with
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
  obtain ⟨row,own,member,ownRead,nonempty,second,changed⟩ := positive
  obtain ⟨index,original,input,fields,unchanged⟩ := link.positive member ownRead nonempty
  exact ⟨constructed,loaded_found,full_done,output,index,original,row,own,
    input,member,ownRead,nonempty,fields,unchanged,second,changed⟩

/-- Initial raw-field allocation derives a full Local reduction and positive positional row origin. -/
private theorem full_precheck_reduce :
    built = .done root heap ∧
    SourceEqualityConstraintFieldLookup.load raw expandedBefore.operations.constraints = .ok (some loaded) ∧
    fullReduced = .done fullResults fullAfter fullSaved fullCurrent ∧ fullResults[0]? = some fullResult ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges fullResult ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := full_witness



private def parentSymbol : Symbol := ("parent",.top)
private def parent := SourceCurrentAllocatedParentWorker.edge 4 0 16 12 16 64 16 16 256 0
  parentSymbol raw neutral.stored values expandedBefore fourth memo
private def parentResult : EdgeValue Symbol Guard := match parent with
  | .done value .. => value | _ => (run (makeEdge parentSymbol top []) empty).1
private def parentAfter := parent.state
private def parentSaved := parent.fourth
private def parentCurrent := parent.memo
private theorem parent_done : parent = .done parentResult parentAfter parentSaved parentCurrent := by
  have tag : (match parent with | .done .. => true | _ => false) = true := by cbv
  cases found : parent <;> simp_all only [parentResult,parentAfter,parentSaved,parentCurrent,
    SourceCurrentAllocatedParentWorker.Outcome.state,SourceCurrentAllocatedParentWorker.Outcome.fourth,
    SourceCurrentAllocatedParentWorker.Outcome.memo,Bool.false_eq_true]
private theorem parent_child : parentResult.children[0]? = some fullResult := by cbv



private theorem parent_witness :
    built = .done root heap ∧
    SourceEqualityConstraintFieldLookup.load raw expandedBefore.operations.constraints = .ok (some loaded) ∧
    parent = .done parentResult parentAfter parentSaved parentCurrent ∧
    parentResult.children[0]? = some fullResult ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges fullResult ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := by
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  have resident : InternedNestedProvenance.Values heap values := by
    intro value member
    cases List.mem_singleton.mp member
    exact available
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
    simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
      (fun guard : Guard => SourceMemoGate.plain guard = true) expression
  have link := SourceCurrentActualParentRowOrigins.edge parent_done expanded_good
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (by intro _; exact ⟨⟨raw_cached,loaded,loaded_found⟩,neutral_ready,resident⟩)
    guards 0 1 raw_footprint rfl parent_child
  obtain ⟨_,_,_,_,_,_,row,own,_,member,ownRead,nonempty,_,_,second,changed⟩ := full_witness
  obtain ⟨index,original,input,fields,unchanged⟩ := link.positive member ownRead nonempty
  exact ⟨constructed,loaded_found,parent_done,parent_child,index,original,row,own,
    input,member,ownRead,nonempty,fields,unchanged,second,changed⟩

/-- A literal Parent return retains a positive source row and its exact recursive continuation. -/
theorem live_parent :
    built = .done root heap ∧
    SourceEqualityConstraintFieldLookup.load raw expandedBefore.operations.constraints = .ok (some loaded) ∧
    parent = .done parentResult parentAfter parentSaved parentCurrent ∧
    parentResult.children[0]? = some fullResult ∧
    ∃ (sourceIndex : Nat) (original row : EdgeValue Symbol Guard) (own : List SourceEqualityClassOrder.Record),
      (nodeEdges root)[sourceIndex]? = some original ∧ row ∈ nodeEdges fullResult ∧
      SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some own) ∧ own ≠ [] ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? ∧
      row.children[1]? = some right ∧ (row.children[0]?.getD (Value.empty : Value Symbol Guard)).referenceOf ≠ left.referenceOf := parent_witness

private def badChild : Value Symbol Guard := .reference (.interned 999)
private theorem badChild_unavailable : ¬ Available heap badChild := by
  intro available
  obtain ⟨key,found⟩ := available.issued 999 (by cbv; exact List.mem_cons_self)
  have missing : heap.nodes.issued 999 = none := by cbv
  rw [missing] at found
  cases found
private def falseGuard : Guard := ⟨none,.top⟩
private def rawRejected := SourceCurrentAllocatedParentWorker.edge 0 0 0 0 0 0 0 0 0 0
  parentSymbol falseGuard .contradiction [badChild] (before 16) fourth memo
private def checkedRejected := SourceCurrentAllocatedParentWorker.edge 0 0 0 0 0 0 0 0 0 0
  parentSymbol ownGuard .contradiction values (before 16) fourth memo
private def rawSentinel : EdgeValue Symbol Guard := match rawRejected with
  | .done value .. => value | _ => (run (makeEdge parentSymbol top []) empty).1
private def checkedSentinel : EdgeValue Symbol Guard := match checkedRejected with
  | .done value .. => value | _ => (run (makeEdge parentSymbol top []) empty).1
private theorem rejection_witness :
    ¬ Available heap badChild ∧
    rawRejected = .done rawSentinel rawRejected.state rawRejected.fourth rawRejected.memo ∧
    rawSentinel.children = [.empty] ∧ rawSentinel.entry.key.constraint = top ∧
    checkedRejected = .done checkedSentinel checkedRejected.state checkedRejected.fourth checkedRejected.memo ∧
    checkedSentinel.children = [.empty] ∧ checkedSentinel.entry.key.constraint = top := by
  have rawDone : rawRejected = .done rawSentinel rawRejected.state rawRejected.fourth rawRejected.memo := by
    have tag : (match rawRejected with | .done .. => true | _ => false) = true := by cbv
    cases found : rawRejected <;> simp_all only [rawSentinel,
      SourceCurrentAllocatedParentWorker.Outcome.state,SourceCurrentAllocatedParentWorker.Outcome.fourth,
      SourceCurrentAllocatedParentWorker.Outcome.memo,Bool.false_eq_true]
  have checkedDone : checkedRejected = .done checkedSentinel checkedRejected.state checkedRejected.fourth checkedRejected.memo := by
    have tag : (match checkedRejected with | .done .. => true | _ => false) = true := by cbv
    cases found : checkedRejected <;> simp_all only [checkedSentinel,
      SourceCurrentAllocatedParentWorker.Outcome.state,SourceCurrentAllocatedParentWorker.Outcome.fourth,
      SourceCurrentAllocatedParentWorker.Outcome.memo,Bool.false_eq_true]
  exact ⟨badChild_unavailable,rawDone,by cbv,by cbv,checkedDone,by cbv,by cbv⟩

/-- Zero lower fuels retain both the raw-reject and checked-reject Empty sentinels. -/
theorem rejection_sentinels :
    ¬ Available heap badChild ∧
    rawRejected = .done rawSentinel rawRejected.state rawRejected.fourth rawRejected.memo ∧
    rawSentinel.children = [.empty] ∧ rawSentinel.entry.key.constraint = top ∧
    checkedRejected = .done checkedSentinel checkedRejected.state checkedRejected.fourth checkedRejected.memo ∧
    checkedSentinel.children = [.empty] ∧ checkedSentinel.entry.key.constraint = top := rejection_witness

end MicroCFTA.ParentSelectedKernels
