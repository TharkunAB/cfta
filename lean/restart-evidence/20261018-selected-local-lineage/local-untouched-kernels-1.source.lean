import MicroCFTA.SourceCurrentActualLocalRowOrigins
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.LocalUntouchedCheck
noncomputable section
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedSharedEditWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def own : Guard := ⟨some [[[0],[1]]],.top⟩
private def trackedPlan : Syntax Symbol Guard := .binder true (.node
  [.mk ("a",.top) plain [],.mk ("p",.top) own [.var 0,.var 0]])
private def tau : Syntax Symbol Guard := .binder false (.node
  [.mk ("leaf",.top) plain [],.mk ("pair",.top) plain [.var 0,.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) plain [trackedPlan,
  .node [.mk ("pair",.top) plain [tau,tau]]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def values := children root
private def firstAllocation := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def first : SourceEqualityConstraintAllocation.Value := match firstAllocation.1 with
  | .ok value => value | _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct plain.equalities firstAllocation.2
private def allocated : SourceEqualityConstraintAllocation.Value := match allocation.1 with
  | .ok value => value | _ => .contradiction
private def before : SourceEqualityNativeDemand.State 10 :=
  ⟨initial 10 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private theorem built_done : built = .done root heap := by cbv
private theorem own_cached : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready before := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState firstAllocation.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) own_cached (show firstAllocation = (.ok first,firstAllocation.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [own,plain] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      one SourceEqualityGuardReadback.empty_cached (show allocation = (.ok allocated,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [own,plain] := by
    intro guard member
    simp only [expression,trackedPlan,tau,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 10 history Cache.empty_valid
    expression covered root heap built_done).1
private instance : DecidableEq Node := by classical exact inferInstance
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[1,0],[1,1]]).getD ⟨.empty,[]⟩
private theorem record_paths : record.paths = [[1,0],[1,1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[1,0],[1,1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(1,.branch [(0,.terminal),(1,.terminal)])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem unselected : SourceCurrentClassPositionalFootprints.Unselected record 0 1 := by
  intro path member
  rw [record_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
  · rcases List.mem_cons.mp member with rfl | member
    · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
    · cases member
private theorem untouched : ∀ path ∈ record.paths, ¬ [Int.ofNat 0].IsPrefix (path.map Int.ofNat) := by
  intro path member
  rw [record_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · decide
  · rcases List.mem_cons.mp member with rfl | member
    · decide
    · cases member
private theorem coherent_all : ∀ own ∈ [record], SourceEqualityClassOrder.Coherent own := by
  intro own member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst own
  exact coherent
private theorem unselected_all : ∀ own ∈ [record], SourceCurrentClassPositionalFootprints.Unselected own 0 1 := by
  intro own member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst own
  exact unselected
private theorem untouched_all : ∀ own ∈ [record], ∀ path ∈ own.paths, ¬ [Int.ofNat 0].IsPrefix (path.map Int.ofNat) := by
  intro own member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst own
  exact untouched
private theorem good : SourceCurrentNativeOperationHeap.Good before :=
  ⟨⟨initial_ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    initial_ready.good.heap,initial_ready.good.operations,initial_ready.good.fields,initial_ready.semantic,initial_ready.costs⟩
private theorem available : InternedNestedProvenance.Values heap values :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done).children
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) expression
private def tracked : Node := values[0]?.getD .empty
private def fourth : SourceCurrentEmptinessMemo.Memo := SourceCurrentEmptinessMemo.empty
private def scanned := SourceCurrentAllocatedRecordScanWorker.scan 4 8 16 32 256 8 values [record] before fourth
private def scanResult : SourceCurrentAllocatedRecordScanWorker.Result :=
  match scanned with | .done result _ _ => result | _ => (none,[])
private def scanState := scanned.state
private def scanMemo := scanned.memo
private theorem scan_done : scanned = .done scanResult scanState scanMemo := by
  have tag : (match scanned with | .done .. => true | _ => false) = true := by cbv
  cases found : scanned <;> simp_all only [scanResult,scanState,scanMemo,
    SourceCurrentAllocatedScanWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.memo,Bool.false_eq_true]
private theorem retained : scanResult = (none,[record]) := by cbv
private def paths := SourceEqualitySelectedRequired.paths (scanResult.2.map SourceEqualityClassOrder.Record.paths)
private def required := SourceEqualityRequiredExecution.requireAll 16 32 paths values scanState.native.machine.heap
private def prepared : List Node := match required with | .done values _ => values | _ => []
private def preparedHeap := match required with
  | .done _ state | .pending _ state | .unresolved _ state | .exhausted _ state => state
private def preparedBefore := SourceCurrentConjunctionClassScan.advanceHeap scanState preparedHeap
private def passed := SourceCurrentAllocatedClassWorker.pass 8 16 32 16 16 256 scanResult.2
  prepared preparedBefore SourceCurrentMemoMergeGraph.empty
private def results : List Node := match passed with | .done values .. => values | _ => []
private def result : Node := results[0]?.getD .empty
private theorem required_done : required = .done prepared preparedHeap := by
  have tag : (match required with | .done .. => true | _ => false) = true := by cbv
  cases found : required <;> simp_all only [prepared,preparedHeap,Bool.false_eq_true]
private theorem passed_done : passed = .done results passed.state passed.memo := by
  have tag : (match passed with | .done .. => true | _ => false) = true := by cbv
  cases found : passed <;> simp_all only [results,SourceCurrentAllocatedClassWorker.Outcome.state,
    SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]
private theorem tracked_input : values[0]? = some tracked := by cbv
private theorem prepared_input : prepared[0]? = some tracked := by cbv
private theorem output : results[0]? = some result := by cbv
private theorem result_nonempty : result ≠ .empty := by cbv; intro same; cases same
private theorem tracked_not_root : ¬ SourceCurrentActualRequiredRowOrigins.Root tracked := by cbv
private theorem tracked_mu : (match tracked with | .mu _ _ _ _ _ true _ => True | _ => False) := by cbv
private theorem unchanged : result = tracked := by
  have same := SourceCurrentActualLocalRowOrigins.untouched_pass passed_done
    (by simpa only [retained] using coherent_all) 0 1
    (by simpa only [retained] using unselected_all)
    (by simpa only [retained] using untouched_all) prepared_input output
  exact same.resolve_left result_nonempty
private def localRun := SourceCurrentAllocatedLocalWorker.classes 4 8 16 8 16 32 16 16 256 8
  [record] values before fourth SourceCurrentMemoMergeGraph.empty
private theorem local_done : localRun = .done results passed.state scanMemo passed.memo := by
  unfold localRun SourceCurrentAllocatedLocalWorker.classes SourceCurrentAllocatedLocalWorker.scan
  change (scanned.bind _) = _
  rw [scan_done]
  simp only [SourceCurrentAllocatedLocalWorker.Outcome.bind,retained]
  unfold SourceCurrentAllocatedLocalWorker.required
  change (match required with | .done values state => _ | .pending _ state => _
    | .unresolved _ state => _ | .exhausted _ state => _).bind _ = _
  rw [required_done]
  simp only [SourceCurrentAllocatedLocalWorker.Outcome.bind]
  change (match passed with | .done values checked memo => _ | .failed fault shared => _) = _
  rw [passed_done]
private theorem link : SourceCurrentActualRequiredRowOrigins.Link 1 tracked result :=
  SourceCurrentActualLocalRowOrigins.classes local_done good (SourceCurrentMemoMergeEffects.stored_empty _)
    available guards coherent_all 0 1 unselected_all tracked_input output
private theorem witness :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    SourceCurrentNativeOperationHeap.Good before ∧
    SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Guard => SourceMemoGate.plain guard = true) heap ∧
    (match tracked with | .mu _ _ _ _ _ true _ => True | _ => False) ∧
    ¬ SourceCurrentActualRequiredRowOrigins.Root tracked ∧
    record.paths = [[1,0],[1,1]] ∧ SourceEqualityClassOrder.Coherent record ∧
    scanResult = (none,[record]) ∧ scanned = .done scanResult scanState scanMemo ∧
    required = .done prepared preparedHeap ∧ passed = .done results passed.state passed.memo ∧
    localRun = .done results passed.state scanMemo passed.memo ∧
    result ≠ .empty ∧ result = tracked ∧ SourceCurrentActualRequiredRowOrigins.Link 1 tracked result := by
  exact ⟨built_done,initial_ready,good,guards,tracked_mu,tracked_not_root,record_paths,coherent,
    retained,scan_done,required_done,passed_done,local_done,result_nonempty,unchanged,link⟩

/-- An actual retained sibling class leaves a constrained smart recursive slot unchanged. -/
theorem constrained_slot_untouched :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    SourceCurrentNativeOperationHeap.Good before ∧
    SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Guard => SourceMemoGate.plain guard = true) heap ∧
    (match tracked with | .mu _ _ _ _ _ true _ => True | _ => False) ∧
    ¬ SourceCurrentActualRequiredRowOrigins.Root tracked ∧
    record.paths = [[1,0],[1,1]] ∧ SourceEqualityClassOrder.Coherent record ∧
    scanResult = (none,[record]) ∧ scanned = .done scanResult scanState scanMemo ∧
    required = .done prepared preparedHeap ∧ passed = .done results passed.state passed.memo ∧
    localRun = .done results passed.state scanMemo passed.memo ∧
    result ≠ .empty ∧ result = tracked ∧ SourceCurrentActualRequiredRowOrigins.Link 1 tracked result := witness

end
end MicroCFTA.LocalUntouchedCheck
