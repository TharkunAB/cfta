import MicroCFTA.SourceCurrentActualTargetSlotHistory
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

namespace MicroCFTA.SlotHistoryKernels
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
private def expression : Syntax Symbol Guard := .node [
  .mk ("first",.top) ownGuard [tau,tau],.mk ("second",.top) ownGuard [tau,tau]]
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
      (by simp [expression,tau,SourceEqualityAnnotationConstruction.Allowed,
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
  (SourceEqualityClassOrder.recordOf [[0,0],[1]]).getD ⟨.empty,[]⟩
private def records := [record,record]
private def values : List (Value Symbol Guard) := [root,left]
private def fourth : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private def memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard := SourceCurrentMemoMergeGraph.empty
private theorem record_paths : record.paths = [[0,0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.terminal)]),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked


private def initialShared := SourceCurrentAllocatedSharedTargetState.initial (before 16) memo
private def entries : List (Int × SourceEqualityEdits.Edits EqualityNormalize.Path) := [(0,.editAt [0,0])]
private def recur := SourceCurrentAllocatedSharedEditWorker.edit (width := 16) record values 1 8 64 64 32 256
private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("fallback",.top) top []) empty).1
private def row0 := ((nodeEdges root)[0]?).getD fallback
private def row1 := ((nodeEdges root)[1]?).getD fallback
private theorem source_rows : nodeEdges root = [row0,row1] := by cbv
private theorem row_fields : row0.entry.key.constraint = ownGuard ∧ row1.entry.key.constraint = ownGuard ∧
    row0.entry.key.symbol ≠ row1.entry.key.symbol ∧ row0.children = [left,left] ∧ row1.children = [left,left] := by
  refine ⟨by cbv,by cbv,?_,by cbv,by cbv⟩
  intro same
  have sizes := congrArg (fun symbol : Symbol => symbol.1.length) same
  cbv at sizes
private def earlierRows := SourceCurrentAllocatedSharedEditWorker.rows recur entries [row0] initialShared
private def rowStart := earlierRows.state
private theorem prefix_done : earlierRows = .done [row0] rowStart := by
  have tag : (match earlierRows with | .done rows _ => some rows | _ => none) = some [row0] := by cbv
  cases found : earlierRows with
  | failed => simp only [found] at tag; cases tag
  | done rows checked =>
    simp only [found] at tag
    cases Option.some.inj tag
    simp only [rowStart,found,SourceCurrentAllocatedSharedEditWorker.Outcome.state]
private def whole := SourceCurrentAllocatedSharedEditWorker.rows recur entries (nodeEdges root) initialShared
private def rowAfter := whole.state
private theorem whole_done : whole = .done [row0,row1] rowAfter := by
  have tag : (match whole with | .done rows _ => some rows | _ => none) = some [row0,row1] := by cbv
  cases found : whole with
  | failed => simp only [found] at tag; cases tag
  | done rows checked =>
    simp only [found] at tag
    cases Option.some.inj tag
    simp only [rowAfter,found,SourceCurrentAllocatedSharedEditWorker.Outcome.state]
private theorem suffix_done : SourceCurrentAllocatedSharedEditWorker.rows recur entries [row1] rowStart =
    .done [row1] rowAfter := by cbv
private def secondLeaf := SourceCurrentAllocatedSharedEditWorker.leaf 8 64 64 32 256 record values [0,0] left rowStart
private def afterLeaf := secondLeaf.state
private theorem second_done : secondLeaf = .done left afterLeaf := by
  have tag : (match secondLeaf with | .done value _ => some value | _ => none) = some left := by cbv
  cases found : secondLeaf with
  | failed => simp only [found] at tag; cases tag
  | done value checked =>
    simp only [found] at tag
    cases Option.some.inj tag
    simp only [afterLeaf,found,SourceCurrentAllocatedSharedEditWorker.Outcome.state]
private theorem slot_written : initialShared.targets [0,0] = none ∧ rowStart.targets [0,0] = some left := by
  exact ⟨rfl,by cbv⟩
private theorem zero_force : SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values [0,0] rowStart =
    .done left rowStart := SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record values [0,0] rowStart left slot_written.2
private theorem first_row_siblings : SourceCurrentAllocatedSharedEditWorker.children recur entries 1
    (row0.children.drop 1) (SourceCurrentAllocatedSharedEditWorker.leaf 8 64 64 32 256 record values [0,0] left initialShared).state =
    .done [left] (SourceCurrentAllocatedSharedEditWorker.leaf 8 64 64 32 256 record values [0,0] left initialShared).state := by
  rw [row_fields.2.2.2.1]
  rfl
private def classRun := SourceCurrentAllocatedClassWorker.runClass 2 8 64 64 32 256 record values (before 16) memo
private def classResults : List (Value Symbol Guard) := match classRun with | .done values .. => values | _ => []
private def classAfter := classRun.state
private def classMemo := classRun.memo
private theorem class_done : classRun = .done classResults classAfter classMemo := by
  have tag : (match classRun with | .done .. => true | _ => false) = true := by cbv
  cases found : classRun <;> simp_all only [classResults,classAfter,classMemo,
    SourceCurrentAllocatedClassWorker.Outcome.state,SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]

private theorem source_values : InternedNestedProvenance.Values heap values := by
  have known := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  intro value member
  change value ∈ [root,left] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact known
  · have same : value = left := List.mem_singleton.mp member
    exact same ▸ originals.1
private theorem initial_shared_good : SourceCurrentLowerOperationInvariants.SharedGood initialShared :=
  SourceCurrentLowerOperationInvariants.SharedGood.initial (physical_good 16)
    (SourceCurrentMemoMergeEffects.stored_empty heap)
private theorem prefix_history : SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values initialShared rowStart :=
  SourceCurrentActualTargetSlotHistory.rows_history recur
    (fun _ _ _ _ _ actual => SourceCurrentActualTargetSlotHistory.edit_history actual) prefix_done
private theorem warm_force : SourceCurrentAllocatedSharedTargetWorker.force 8 64 64 32 256 record values [0,0] rowStart =
    .done left rowStart := SourceCurrentAllocatedSharedTargetWorker.force_hit 8 64 64 32 256 record values [0,0] rowStart left slot_written.2

private def firstLeaf := SourceCurrentAllocatedSharedEditWorker.leaf 8 64 64 32 256 record values [0,0] left initialShared
private def firstAfter := firstLeaf.state
private theorem first_done : firstLeaf = .done left firstAfter := by
  have tag : (match firstLeaf with | .done value _ => some value | _ => none) = some left := by cbv
  cases found : firstLeaf with
  | failed => simp only [found] at tag; cases tag
  | done value checked =>
    simp only [found] at tag
    cases Option.some.inj tag
    simp only [firstAfter,found,SourceCurrentAllocatedSharedEditWorker.Outcome.state]

private theorem witness :
    built = .done root heap ∧ record.paths = [[0,0],[1]] ∧
    SourceEqualityClassOrder.Coherent record ∧
    SourceCurrentLowerOperationInvariants.SharedGood initialShared ∧
    InternedNestedProvenance.Values heap values ∧
    nodeEdges root = [row0,row1] ∧
    row0.entry.key.constraint = ownGuard ∧ row1.entry.key.constraint = ownGuard ∧
    row0.entry.key.symbol ≠ row1.entry.key.symbol ∧
    row0.children = [left,left] ∧ row1.children = [left,left] ∧
    classRun = .done classResults classAfter classMemo ∧
    earlierRows = .done [row0] rowStart ∧
    whole = .done [row0,row1] rowAfter ∧
    SourceCurrentAllocatedSharedEditWorker.rows recur entries [row1] rowStart = .done [row1] rowAfter ∧
    initialShared.targets [0,0] = none ∧ rowStart.targets [0,0] = some left ∧
    SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values [0,0] rowStart = .done left rowStart ∧
    SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values initialShared rowStart ∧
    ∃ firstTarget firstMiddle firstChecked firstSaved writer writerChecked writerSaved secondChecked count,
      firstLeaf = .done left firstAfter ∧
      SourceCurrentAllocatedSharedTargetWorker.force 8 64 64 32 256 record values [0,0] initialShared =
        .done firstTarget firstMiddle ∧
      SourceCurrentAllocatedTargetWorker.target 8 64 64 32 256 values
        (SourceEqualityClassTarget.operandPaths record.paths [0,0]) initialShared.checked initialShared.memo =
          .done firstTarget firstChecked firstSaved ∧
      firstMiddle = SourceCurrentAllocatedSharedTargetState.store initialShared [0,0] firstTarget firstChecked firstSaved ∧
      SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values initialShared writer ∧
      writer.targets [0,0] = none ∧
      SourceCurrentAllocatedTargetWorker.target 8 64 64 32 256 values
        (SourceEqualityClassTarget.operandPaths record.paths [0,0]) writer.checked writer.memo =
          .done left writerChecked writerSaved ∧
      SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values
        (SourceCurrentAllocatedSharedTargetState.store writer [0,0] left writerChecked writerSaved) rowStart ∧
      secondLeaf = .done left afterLeaf ∧
      SourceCurrentAllocatedSharedTargetWorker.force 8 64 64 32 256 record values [0,0] rowStart = .done left rowStart ∧
      SourceEqualityNativeDemand.execute 256
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left left)) rowStart.checked =
          .done left secondChecked ∧
      afterLeaf = SourceCurrentAllocatedSharedTargetState.advance rowStart secondChecked ∧
      afterLeaf.targets = rowStart.targets ∧ afterLeaf.memo = rowStart.memo ∧
      count < 256 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left left)) rowStart.checked
        (.code (.pure left)) secondChecked
 := by
  obtain ⟨firstTarget,firstMiddle,firstNative,firstForced,_firstQuery,_firstAdvance,_⟩ :=
    SourceCurrentActualSharedLeafEvents.leaf first_done
  rcases SourceCurrentActualSharedLeafEvents.force firstForced with hit | ⟨_missing,firstChecked,firstSaved,targetDone,stored⟩
  · rw [slot_written.1] at hit
    cases hit.1
  · obtain ⟨writer,writerChecked,writerSaved,earlier,missing,written,later⟩ :=
      SourceCurrentActualTargetSlotHistory.force_writer prefix_history slot_written.1 warm_force
    obtain ⟨secondTarget,secondMiddle,secondChecked,secondForced,queried,advanced,targets,memos,count,bound,steps⟩ :=
      SourceCurrentActualSharedLeafEvents.leaf second_done
    have equal : SourceCurrentAllocatedSharedTargetWorker.Outcome.done left rowStart =
        .done secondTarget secondMiddle := warm_force.symm.trans secondForced
    cases equal
    exact ⟨constructed,record_paths,coherent,initial_shared_good,source_values,source_rows,
      row_fields.1,row_fields.2.1,row_fields.2.2.1,row_fields.2.2.2.1,row_fields.2.2.2.2,
      class_done,prefix_done,whole_done,suffix_done,slot_written.1,slot_written.2,zero_force,prefix_history,
      firstTarget,firstMiddle,firstChecked,firstSaved,writer,writerChecked,writerSaved,secondChecked,count,
      first_done,firstForced,targetDone,stored,earlier,missing,written,later,second_done,warm_force,
      queried,advanced,targets,memos,bound,steps⟩

/-- Repeated row leaves recover the earlier literal target writer and retain the actual warm native call. -/
theorem repeated_row_target_history :
    built = .done root heap ∧ record.paths = [[0,0],[1]] ∧
    SourceEqualityClassOrder.Coherent record ∧
    SourceCurrentLowerOperationInvariants.SharedGood initialShared ∧
    InternedNestedProvenance.Values heap values ∧
    nodeEdges root = [row0,row1] ∧
    row0.entry.key.constraint = ownGuard ∧ row1.entry.key.constraint = ownGuard ∧
    row0.entry.key.symbol ≠ row1.entry.key.symbol ∧
    row0.children = [left,left] ∧ row1.children = [left,left] ∧
    classRun = .done classResults classAfter classMemo ∧
    earlierRows = .done [row0] rowStart ∧
    whole = .done [row0,row1] rowAfter ∧
    SourceCurrentAllocatedSharedEditWorker.rows recur entries [row1] rowStart = .done [row1] rowAfter ∧
    initialShared.targets [0,0] = none ∧ rowStart.targets [0,0] = some left ∧
    SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values [0,0] rowStart = .done left rowStart ∧
    SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values initialShared rowStart ∧
    ∃ firstTarget firstMiddle firstChecked firstSaved writer writerChecked writerSaved secondChecked count,
      firstLeaf = .done left firstAfter ∧
      SourceCurrentAllocatedSharedTargetWorker.force 8 64 64 32 256 record values [0,0] initialShared =
        .done firstTarget firstMiddle ∧
      SourceCurrentAllocatedTargetWorker.target 8 64 64 32 256 values
        (SourceEqualityClassTarget.operandPaths record.paths [0,0]) initialShared.checked initialShared.memo =
          .done firstTarget firstChecked firstSaved ∧
      firstMiddle = SourceCurrentAllocatedSharedTargetState.store initialShared [0,0] firstTarget firstChecked firstSaved ∧
      SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values initialShared writer ∧
      writer.targets [0,0] = none ∧
      SourceCurrentAllocatedTargetWorker.target 8 64 64 32 256 values
        (SourceEqualityClassTarget.operandPaths record.paths [0,0]) writer.checked writer.memo =
          .done left writerChecked writerSaved ∧
      SourceCurrentActualTargetSlotHistory.History 8 64 64 32 256 record values
        (SourceCurrentAllocatedSharedTargetState.store writer [0,0] left writerChecked writerSaved) rowStart ∧
      secondLeaf = .done left afterLeaf ∧
      SourceCurrentAllocatedSharedTargetWorker.force 8 64 64 32 256 record values [0,0] rowStart = .done left rowStart ∧
      SourceEqualityNativeDemand.execute 256
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left left)) rowStart.checked =
          .done left secondChecked ∧
      afterLeaf = SourceCurrentAllocatedSharedTargetState.advance rowStart secondChecked ∧
      afterLeaf.targets = rowStart.targets ∧ afterLeaf.memo = rowStart.memo ∧
      count < 256 ∧ SourceEqualityNativeDemand.Steps count
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left left)) rowStart.checked
        (.code (.pure left)) secondChecked
 := witness

end MicroCFTA.SlotHistoryKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SlotHistoryKernels.repeated_row_target_history
#print MicroCFTA.SlotHistoryKernels.repeated_row_target_history
#print axioms MicroCFTA.SlotHistoryKernels.repeated_row_target_history
