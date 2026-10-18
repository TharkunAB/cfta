import MicroCFTA.SourceCurrentPositionalOriginChain
import MicroCFTA.SourceCurrentActualClassDispatch
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentLowerOperationInvariants
import MicroCFTA.SourceCurrentAllocatedInheritedPrefix
import MicroCFTA.SourceEqualityNormalizationReceipt

/-!
# A selected positive continuation can come from the competing slot

The actual class worker returns a positive row and a positive child.
That child occurs in the competing input and not in the selected original.
The original-slot positional Below relation therefore does not hold.
The actual inherited prefix also drops the cross-child equality on descent.
This example establishes no infinite execution or implementation defect.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.SourceCurrentSelectedRenewalBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := ⟨some [],.top⟩
private def equal : Guard := ⟨some [[[0],[1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) top []]
private def plainMid : Syntax Symbol Guard := .node [.mk ("mid",.top) top [leaf,leaf]]
private def positiveMid : Syntax Symbol Guard := .node [.mk ("mid",.top) equal [leaf,leaf]]
private def firstPlan : Syntax Symbol Guard := .node [.mk ("root",.top) equal [plainMid,plainMid]]
private def secondPlan : Syntax Symbol Guard := .node [.mk ("root",.top) top [positiveMid,positiveMid]]
private def expression : Syntax Symbol Guard := .node [.mk ("forest",.top) top [firstPlan,secondPlan]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def inputs := children root
private def first := inputs[0]?.getD .empty
private def second := inputs[1]?.getD .empty
private def one := SourceEqualityConstraintAllocation.construct equal.equalities Cache.emptyState
private def oneValue : EqValue := match one.1 with | .ok value => value | .error _ => .contradiction
private def allocation := SourceEqualityConstraintAllocation.construct top.equalities one.2
private def inherited : EqValue := match allocation.1 with | .ok value => value | .error _ => .contradiction
private def before : Checked 10 :=
  ⟨initial 10 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.initial allocation.2⟩
private def record := (SourceEqualityClassOrder.recordOf [[0],[1]]).getD ⟨.empty,[]⟩
private noncomputable def called := SourceCurrentAllocatedClassWorker.runClass 4 8 8 64 16 128
  record inputs before SourceCurrentMemoMergeGraph.empty
private noncomputable def outputs := match called with | .done values .. => values | .failed .. => []
private noncomputable def result := outputs[0]?.getD .empty
private def fallback := (run (makeEdge ("missing",.top) top []) heap).1
private noncomputable def row := (nodeEdges result)[0]?.getD fallback
private noncomputable def next := row.children[0]?.getD .empty
private noncomputable def nextRow := (nodeEdges next)[0]?.getD fallback
private def firstRow := (nodeEdges first)[0]?.getD fallback
private def secondRow := (nodeEdges second)[0]?.getD fallback
private def records := (SourceEqualityClassOrder.recordsOf [[[0],[1]]]).getD []
private noncomputable def prefixState := SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited called.state.operations
private noncomputable def combined : EqValue := match prefixState.1 with | .ok (some value) => value | _ => .contradiction
private theorem built_done : built = .done root heap := by cbv
private theorem input_shape : inputs = [first,second] := by cbv
private theorem equal_cached : SourceEqualityGuardReadback.Cached equal.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0],[1]]] = .normalized [[[0],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem ready : SourceCurrentConjunctionClassScan.Ready before := by
  have oneHistory : SourceEqualityOriginalAllocationHistory.History Cache.emptyState one.2 [equal] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) equal_cached (show one = (.ok oneValue,one.2) by cbv)
  have history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocation.2 [equal,top] := by
    simpa only [List.cons_append,List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      oneHistory SourceEqualityGuardReadback.empty_cached (show allocation = (.ok inherited,allocation.2) by cbv)
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [equal,top] := by
    intro guard member
    simp only [expression,firstPlan,secondPlan,plainMid,positiveMid,leaf,SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
      List.mem_append,List.mem_cons,List.not_mem_nil,List.nil_append,List.append_nil,or_false,or_self] at member ⊢
    rcases member with rfl | rfl | rfl <;> simp
  exact (SourceCurrentConjunctionClassHistoryEntry.constructed 10 history Cache.empty_valid
    expression covered root heap built_done).1
private theorem good : SourceCurrentNativeOperationHeap.Good before :=
  ⟨⟨ready.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
    ready.good.heap,ready.good.operations,ready.good.fields,ready.semantic,ready.costs⟩
private theorem available : InternedNestedProvenance.Values heap inputs :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done).children
private theorem record_paths : record.paths = [[0],[1]] := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete [[0],[1]]
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0,.terminal),(1,.terminal)],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0],by simp,[1],by simp,by decide⟩
private theorem primary_false : SourceCurrentAllocatedGateWorker.primary 8 inputs record.paths before = .done false before := by cbv
private theorem called_done : called = .done outputs called.state called.memo := by
  have tag : (match called with | .done .. => true | .failed .. => false) = true := by cbv
  cases actual : called with
  | done values state memo => simp only [outputs,actual,SourceCurrentAllocatedClassWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.memo]
  | failed fault state => rw [actual] at tag; cases tag
private theorem facts : outputs[0]? = some result ∧ row ∈ nodeEdges result ∧
    SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records) ∧ records ≠ [] ∧
    row.children[0]? = some next ∧ nextRow ∈ nodeEdges next ∧
    SourceEqualityPhysicalPayload.own nextRow.entry.key.constraint = .ok (some records) ∧
    secondRow ∈ nodeEdges second ∧ secondRow.children[0]? = some next ∧
    firstRow.children[0]? ≠ some next := by
  refine ⟨by cbv,by cbv; exact List.mem_cons_self,by cbv,?_,by cbv,
    by cbv; exact List.mem_cons_self,by cbv,by cbv; exact List.mem_cons_self,by cbv,?_⟩
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
private theorem first_rows : nodeEdges first = [firstRow] := by cbv
private theorem no_below : ¬ SourceCurrentPositionalOriginChain.Below 0 next first := by
  intro below
  obtain ⟨value,edge,classes,linked,member,positive,nonempty,present⟩ := below
  obtain ⟨index,original,found,_origin,unchanged⟩ := linked.positive member positive nonempty
  have same : original = firstRow := by
    have included := List.mem_of_getElem? found
    rw [first_rows] at included
    exact List.mem_singleton.mp included
  subst original
  exact facts.2.2.2.2.2.2.2.2.2 (unchanged.symm.trans present)
private theorem dropped : inherited.payload = some [] ∧ prefixState.1 = .ok (some combined) ∧
    (SourceEqualityConstraintMemoAllocation.descend combined 0 prefixState.2).1.payload = some [] := by cbv

private theorem witness :
    ∃ (source : Syntax Symbol Guard) (root first second result next : Node) (heap : State Symbol Guard)
      (before after : Checked 10) (saved : Memo) (record : SourceEqualityClassOrder.Record) (outputs : List Node)
      (row nextRow competing : EdgeValue Symbol Guard) (classes : List SourceEqualityClassOrder.Record)
      (inherited combined : EqValue),
      InternedFreshOrdinaryConstruction.build source [] empty = .done root heap ∧ children root = [first,second] ∧
      before.native.machine.heap = heap ∧ SourceCurrentNativeOperationHeap.Good before ∧
      InternedNestedProvenance.Values heap [first,second] ∧
      record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
      SourceCurrentAllocatedGateWorker.primary 8 [first,second] record.paths before = .done false before ∧
      SourceCurrentAllocatedClassWorker.runClass 4 8 8 64 16 128 record [first,second] before
        SourceCurrentMemoMergeGraph.empty = .done outputs after saved ∧ outputs[0]? = some result ∧
      row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some classes) ∧
      classes ≠ [] ∧ row.children[0]? = some next ∧ nextRow ∈ nodeEdges next ∧
      SourceEqualityPhysicalPayload.own nextRow.entry.key.constraint = .ok (some classes) ∧
      competing ∈ nodeEdges second ∧ competing.children[0]? = some next ∧
      (∀ original ∈ nodeEdges first, original.children[0]? ≠ some next) ∧
      ¬ SourceCurrentPositionalOriginChain.Below 0 next first ∧ inherited.payload = some [] ∧
      (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited after.operations).1 = .ok (some combined) ∧
      (SourceEqualityConstraintMemoAllocation.descend combined 0
        (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited after.operations).2).1.payload = some [] := by
  refine ⟨expression,root,first,second,result,next,heap,before,called.state,called.memo,record,outputs,row,nextRow,
    secondRow,records,inherited,combined,built_done,input_shape,rfl,good,?_,record_paths,coherent,active,?_,?_,
    facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2.1,
    facts.2.2.2.2.2.2.1,facts.2.2.2.2.2.2.2.1,facts.2.2.2.2.2.2.2.2.1,?_,no_below,dropped.1,dropped.2.1,dropped.2.2⟩
  · simpa only [input_shape] using available
  · simpa only [input_shape] using primary_false
  · simpa only [input_shape] using called_done
  · intro original member
    rw [first_rows] at member
    cases List.mem_singleton.mp member
    exact facts.2.2.2.2.2.2.2.2.2

/-- Actual selected class execution need not preserve the selected original's positional anchor. -/
theorem selected_competing_continuation :
    ∃ (source : Syntax Symbol Guard) (root first second result next : Node) (heap : State Symbol Guard)
      (before after : Checked 10) (saved : Memo) (record : SourceEqualityClassOrder.Record) (outputs : List Node)
      (row nextRow competing : EdgeValue Symbol Guard) (classes : List SourceEqualityClassOrder.Record)
      (inherited combined : EqValue),
      InternedFreshOrdinaryConstruction.build source [] empty = .done root heap ∧ children root = [first,second] ∧
      before.native.machine.heap = heap ∧ SourceCurrentNativeOperationHeap.Good before ∧
      InternedNestedProvenance.Values heap [first,second] ∧
      record.paths = [[0],[1]] ∧ SourceEqualityClassOrder.Coherent record ∧ EqualityNormalize.Nontrivial record.paths ∧
      SourceCurrentAllocatedGateWorker.primary 8 [first,second] record.paths before = .done false before ∧
      SourceCurrentAllocatedClassWorker.runClass 4 8 8 64 16 128 record [first,second] before
        SourceCurrentMemoMergeGraph.empty = .done outputs after saved ∧ outputs[0]? = some result ∧
      row ∈ nodeEdges result ∧ SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some classes) ∧
      classes ≠ [] ∧ row.children[0]? = some next ∧ nextRow ∈ nodeEdges next ∧
      SourceEqualityPhysicalPayload.own nextRow.entry.key.constraint = .ok (some classes) ∧
      competing ∈ nodeEdges second ∧ competing.children[0]? = some next ∧
      (∀ original ∈ nodeEdges first, original.children[0]? ≠ some next) ∧
      ¬ SourceCurrentPositionalOriginChain.Below 0 next first ∧ inherited.payload = some [] ∧
      (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited after.operations).1 = .ok (some combined) ∧
      (SourceEqualityConstraintMemoAllocation.descend combined 0
        (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited after.operations).2).1.payload = some [] := witness

end MicroCFTA.SourceCurrentSelectedRenewalBoundary
