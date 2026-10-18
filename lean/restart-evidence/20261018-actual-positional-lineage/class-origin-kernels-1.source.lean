import MicroCFTA.SourceCurrentActualClassRowOrigins
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ClassOriginCheck
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
private def leftPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("left",.top) plain []])
private def rightPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("base",.top) plain [],.mk ("loop",.top) plain [.var 0],.mk ("right",.top) plain []])
private def tailPlan : Syntax Symbol Guard := .binder false (.node
  [.mk ("tail",.top) plain [],.mk ("repeat",.top) plain [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots",.top) plain [
  .node [.mk ("pair",.top) own [leftPlan,tailPlan]],
  .node [.mk ("pair",.top) own [rightPlan,tailPlan]]]]
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
    simp only [expression,leftPlan,rightPlan,tailPlan,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] at member ⊢
    simpa only [List.mem_cons,List.not_mem_nil,or_false,or_comm] using member
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 10 history Cache.empty_valid
    expression covered root heap built_done).1
private def record : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[0,0],[1,0]]).getD ⟨.empty,[]⟩
private theorem record_paths : record.paths = [[0,0],[1,0]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0,0],[1,0]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.terminal)]),(1,.branch [(0,.terminal)])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem unselected : SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  intro path member
  rw [record_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
  · rcases List.mem_cons.mp member with rfl | member
    · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
    · cases member

private theorem good : SourceCurrentNativeOperationHeap.Good before :=
  ⟨⟨initial_ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    initial_ready.good.heap,initial_ready.good.operations,initial_ready.good.fields,initial_ready.semantic,initial_ready.costs⟩
private theorem available : InternedNestedProvenance.Values heap values :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done).children
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) heap := by
  simpa only [built,heap] using SourceCurrentConstrainedCapGuardExecution.closed_heap
    (fun guard : Guard => SourceMemoGate.plain guard = true) expression
private def paths : List (List Int) := [[0,0],[1,0]]
private def required := SourceEqualityRequiredExecution.requireAll 16 32 paths values heap
private def prepared : List Node := match required with | .done values _ => values | _ => []
private def preparedHeap := required.state
private def preparedBefore := SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨preparedHeap,before.operations⟩
private def passed := SourceCurrentAllocatedClassWorker.pass 8 16 32 16 16 256 [record,record]
  prepared preparedBefore SourceCurrentMemoMergeGraph.empty
private def results : List Node := match passed with | .done values .. => values | _ => []
private def source : Node := values[1]?.getD .empty
private def result : Node := results[1]?.getD .empty
private def row : EdgeValue Symbol Guard := (nodeEdges result)[0]?.getD (run (makeEdge ("pair",.top) own []) heap).1
private def ownRecords : List SourceEqualityClassOrder.Record :=
  [(SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩]
private theorem required_done : required = .done prepared preparedHeap := by
  have tag : (match required with | .done .. => true | _ => false) = true := by cbv
  cases found : required <;> simp_all only [prepared,preparedHeap,SourceEqualityRequiredWorker.Result.state,Bool.false_eq_true]
private theorem passed_done : passed = .done results passed.state passed.memo := by
  have tag : (match passed with | .done .. => true | _ => false) = true := by cbv
  cases found : passed <;> simp_all only [results,SourceCurrentAllocatedClassWorker.Outcome.state,
    SourceCurrentAllocatedClassWorker.Outcome.memo,Bool.false_eq_true]
private theorem required_unselected : ∀ entries, SourceEqualityNeeded.build paths = .node entries →
    SourceCurrentActualRequiredRowOrigins.Unselected entries 1 1 := by
  intro entries built
  have same : entries = [(0,.node [(0,.node [])]),(1,.node [(0,.node [])])] :=
    SourceEqualityNeeded.Needed.node.inj (built.symm.trans (by cbv))
  subst entries
  intro needed found children shape
  have same : needed = .node [(0,.node [])] := Option.some.inj (by simpa [SourceEqualityNeededMap.lookup] using found.symm)
  cases same
  cases SourceEqualityNeeded.Needed.node.inj shape
  rfl
private theorem coherent_all : ∀ own ∈ [record,record], SourceEqualityClassOrder.Coherent own := by
  intro own member
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  subst own
  exact coherent
private theorem unselected_all : ∀ own ∈ [record,record], SourceCurrentClassPositionalFootprints.Unselected own 1 1 := by
  intro own member
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  subst own
  exact unselected
private theorem input : values[1]? = some source := by cbv
private theorem output : results[1]? = some result := by cbv
private theorem row_member : row ∈ nodeEdges result := by dsimp [row]; cbv; exact .head _
private theorem own_positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some ownRecords) := by
  dsimp [row]
  cbv
private theorem origin : SourceCurrentActualRequiredRowOrigins.Root result ∧
    SourceCurrentActualRequiredRowOrigins.Link 1 source result :=
  SourceCurrentActualClassRowOrigins.prepared_pass required_done passed_done good
    (SourceCurrentMemoMergeEffects.stored_empty _) available guards coherent_all 1 1 required_unselected
    unselected_all input output (by cbv)
private theorem witness :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    SourceCurrentNativeOperationHeap.Good before ∧ paths ≠ [] ∧
    required = .done prepared preparedHeap ∧ passed = .done results passed.state passed.memo ∧
    SourceCurrentActualRequiredRowOrigins.Root result ∧ SourceCurrentActualRequiredRowOrigins.Link 1 source result ∧
    row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some ownRecords) ∧
    ownRecords ≠ [] ∧
    ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), (nodeEdges source)[sourceIndex]? = some original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? := by
  refine ⟨built_done,initial_ready,good,by cbv; intro impossible; cases impossible,
    required_done,passed_done,origin.1,origin.2,row_member,own_positive,by cbv; intro impossible; cases impossible,?_⟩
  exact origin.2.positive row_member own_positive (by cbv; intro impossible; cases impossible)

/-- Actual Required preparation and two classes retain the positive row's indexed original and second child. -/
theorem prepared_positive_row :
    built = .done root heap ∧ SourceCurrentConjunctionClassScan.Ready before ∧
    SourceCurrentNativeOperationHeap.Good before ∧ paths ≠ [] ∧
    required = .done prepared preparedHeap ∧ passed = .done results passed.state passed.memo ∧
    SourceCurrentActualRequiredRowOrigins.Root result ∧ SourceCurrentActualRequiredRowOrigins.Link 1 source result ∧
    row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some ownRecords) ∧
    ownRecords ≠ [] ∧
    ∃ (sourceIndex : Nat) (original : EdgeValue Symbol Guard), (nodeEdges source)[sourceIndex]? = some original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original row ∧ row.children[1]? = original.children[1]? := witness

end
end MicroCFTA.ClassOriginCheck
