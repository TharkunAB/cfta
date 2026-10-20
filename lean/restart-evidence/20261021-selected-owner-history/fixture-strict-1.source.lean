import MicroCFTA.SourceCurrentOuterOwnerSelection
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

/-!
# Actual warm selected owner copy

The OriginalRepeat source family first runs a cold edge call with empty
outer result tables. Owner activation follows that completed call. The
same edge request then reads its returned cell while the owner is active.
One selected-writer consumer retains all original false primary gates.
No descendant or owner result is executed.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000
namespace MicroCFTA.WarmOwnerSelectionFixture
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Origins" => SourceCurrentOuterParentHistory.Origins
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq Node := by classical exact inferInstance
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def plain : Guard := ⟨some [], .top⟩
private def own : Guard := ⟨some [[[0,0],[0,1],[1]]], .top⟩
private def tauPlan : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) plain [], .mk ("pair",.top) plain [.var 0,.var 0]])
private def cPlan : Syntax Symbol Guard := .node [.mk ("pair",.top) own [tauPlan,tauPlan]]
private def program : Syntax Symbol Guard := .node [.mk ("pair",.top) own [cPlan,cPlan]]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def original : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Node := (children original)[0]?.getD .empty
private def tau : Node := (children child)[0]?.getD .empty
private def first := SourceEqualityConstraintAllocation.construct own.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue second.2
private def initial := SourceCurrentAllocatedPartialInitialization.caller 8 second.2 heap
private def owner : NodeRequest := ⟨inherited,original⟩
private def row : Edge := (nodeEdges original)[0]?.getD (run (makeEdge ("pair",.top) own [child,child]) heap).1
private def request : EdgeRequest := ⟨inherited,row⟩
private noncomputable def cold := edgeCall 22 16 16 16 16 16 16 16 16 256 0 request initial
private noncomputable def warmed := cold.state
private noncomputable def returned : Edge := match cold with | .done value _ => value | .failed .. => row
private noncomputable def running := (beginNode owner warmed).2.2
private noncomputable def warm := edgeCall 22 16 16 16 16 16 16 16 16 256 0 request running
private theorem construction : built = .done original heap := by cbv
private def ownValue : EqValue := match first.1 with | .ok value => value | _ => .contradiction
private theorem cached_own : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0,0],[0,1],[1]]] =
      .normalized [[[0,0],[0,1],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [own,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_own (show first = (.ok ownValue,first.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct one SourceEqualityGuardReadback.empty_cached
    (show second = (.ok inherited,second.2) by cbv)
private theorem initial_inputs : SourceCurrentOuterPrefixInvariants.Good initial ∧
    SourceCurrentOuterPrefixInvariants.NodeReady initial owner := by
  have sourceFacts := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid program
    (fun guard member => by
      simp only [program,cPlan,tauPlan,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    original heap construction
  have eq := SourceCurrentAllocatedPartialInitialization.operations_correct second.2
    (history.verified Cache.empty_valid).1
  have good : SourceCurrentNativeOperationHeap.Good initial.checked :=
    ⟨⟨sourceFacts.1.good.native.machine,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩,
      sourceFacts.1.good.heap,eq.1,sourceFacts.1.good.fields.grows eq.2.1,sourceFacts.1.semantic,sourceFacts.1.costs⟩
  exact ⟨SourceCurrentOuterPrefixInvariants.initial initial.checked _ _ good
    (SourceCurrentMemoMergeEffects.stored_empty heap)
    (SourceCurrentMuReconstructionEffects.constructed program original heap construction),eq.2.2,sourceFacts.2.1⟩
private theorem initial_origins : Origins initial :=
  SourceCurrentOuterParentHistory.initial initial.checked _ _
private theorem row_list : nodeEdges original = [row] := by cbv
private theorem row_ready : SourceCurrentOuterPrefixInvariants.EdgeReady initial request := by
  refine ⟨initial_inputs.2.1,?_⟩
  exact resident_edges _ initial_inputs.1.checked.heap.semantic.1.normal.facts.linked original
    initial_inputs.2.2.resident row (by rw [row_list]; exact List.mem_singleton_self _)
private theorem cold_return : cold = .done returned warmed := by cbv
private theorem cold_children : returned.children = [original,child] := by cbv
private theorem began : beginNode owner warmed = (0,.evaluate owner,running) := by cbv
private theorem running_inputs : SourceCurrentOuterPrefixInvariants.Good running ∧
    SourceCurrentOuterPrefixInvariants.NodeReady running owner := by
  have next := SourceCurrentOuterPrefixInvariants.edge_done cold_return initial_inputs.1 row_ready
  exact SourceCurrentOuterPrefixInvariants.activate began next.1
    ⟨initial_inputs.2.1.grows next.2.1.operations.constraint_growth,
      next.2.1.keeps.available original initial_inputs.2.2⟩
private theorem running_origins : Origins running := by
  have retained := (SourceCurrentOuterParentHistory.edge_call cold_return initial_inputs.1 row_ready initial_origins).1
  exact retained
private theorem running_ready : SourceCurrentOuterPrefixInvariants.EdgeReady running request := by
  refine ⟨running_inputs.2.1,?_⟩
  exact resident_edges _ running_inputs.1.checked.heap.semantic.1.normal.facts.linked original
    running_inputs.2.2.resident row (by rw [row_list]; exact List.mem_singleton_self _)
private theorem ordinary_shape (value : Node)
    (ordinary : (match value with | .node .. => true | _ => false) = true) :
    ∃ entry depth free, value = .node entry (nodeEdges value) depth free := by
  cases value <;> simp_all [nodeEdges]
private theorem original_shape : ∃ entry depth free, original = .node entry [row] depth free := by
  simpa only [row_list] using ordinary_shape original (by cbv)
private theorem recursive_shape (value : Node)
    (recursive : (match value with | .mu .. => true | _ => false) = true) :
    ∃ entry body depth ordinary, value = .mu entry body depth ordinary := by
  cases value <;> simp_all
private theorem tau_shape : ∃ entry body depth ordinary, tau = .mu entry body depth ordinary :=
  recursive_shape tau (by cbv)
private theorem computed_receipts :
    inherited.payload = some [] ∧
    children original = [child,child] ∧ children child = [tau,tau] ∧
    SourceMemoGate.unconstrained tau = true ∧ SourceMemoGate.unconstrained original = false ∧
    row.entry.key.constraint = own ∧
    (beginEdge request initial).2.1 = .evaluate request ∧
    warmed.nodeResults = FlatMemoThunk.empty ∧
    warmed.edgeResults.table request.key = some 0 ∧
    warmed.edgeResults.cells 0 = some ⟨request,.returned returned⟩ ∧
    running.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cbv
private theorem warm_ready : beginEdge request running = (0,.ready returned,running) :=
  beginEdge_ready request request running 0 returned
    computed_receipts.2.2.2.2.2.2.2.2.1 computed_receipts.2.2.2.2.2.2.2.2.2.1
private theorem warm_return : warm = .done returned running := by
  simp only [warm,edgeCall,warm_ready]

private theorem checked_witness :
    InternedFreshOrdinaryConstruction.build program [] empty = .done original initial.checked.native.machine.heap ∧
    inherited.payload = some [] ∧
    initial.nodeResults = FlatMemoThunk.empty ∧ initial.edgeResults = FlatMemoThunk.empty ∧
    children original = [child,child] ∧ children child = [tau,tau] ∧
    (∃ entry body depth ordinary, tau = .mu entry body depth ordinary) ∧
    SourceMemoGate.unconstrained tau = true ∧ SourceMemoGate.unconstrained original = false ∧
    row.entry.key.constraint = own ∧
    SourceCurrentOuterPrefixInvariants.Good initial ∧ Origins initial ∧
    (beginEdge request initial).2.1 = .evaluate request ∧
    cold = .done returned warmed ∧ returned.children = [original,child] ∧
    warmed.nodeResults = FlatMemoThunk.empty ∧
    warmed.edgeResults.cells 0 = some ⟨request,.returned returned⟩ ∧
    beginNode owner warmed = (0,.evaluate owner,running) ∧
    running.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
    beginEdge request running = (0,.ready returned,running) ∧
    warm = .done returned running ∧
    SourceCurrentOuterPrefixInvariants.Good running ∧
    SourceCurrentOuterPrefixInvariants.EdgeReady running request ∧
    nodeEdges original = [row] ∧
    Origins running ∧ original = owner.value ∧
    ∃ (wg ws wr we wp wh wm wc wn wbudget : Nat) (writerBefore writerAfter : Checked 8)
      (writerFourth writerSaved : Fourth) (writerMemo writerMerge : Memo),
      SourceCurrentAllocatedParentWorker.edge wg ws wr we wp wh wm wc wn wbudget
        request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
        request.value.children writerBefore writerFourth writerMemo =
          .done returned writerAfter writerSaved writerMerge ∧
      SourceCurrentNativeOperationHeap.Good writerBefore ∧
      SourceCurrentMemoMergeEffects.Stored writerBefore.native.machine.heap writerMemo ∧
      (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
        FieldAvailable writerBefore.operations request.value.entry.key.constraint ∧
        EqReady writerBefore.operations.constraints request.inherited ∧
        Values writerBefore.native.machine.heap request.value.children) ∧
      ∃ (loaded : Allocated) (middle : Checked 8) (records kept : List Record)
      (scanned : Checked 8) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
      SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false ∧
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint writerBefore.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce wg ws wr we wp wh wm wc wn wbudget loaded request.inherited request.value.children
        writerBefore writerFourth writerMemo = .done returned.children middle writerSaved writerMerge ∧
      SourceCurrentAllocatedMkEdge.build request.value.entry.key.symbol loaded returned.children middle = (.ok returned, writerAfter) ∧
      SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
        returned.children.length = true ∧
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard request.inherited writerBefore.operations).1 =
        .ok (.classes records) ∧
      SourceCurrentAllocatedRecordScanWorker.scan wg ws wp wh wn wbudget request.value.children records
        (prefixState writerBefore loaded request.inherited) writerFourth = .done (none, kept) scanned scanFourth ∧
      kept ≠ [] ∧
      SourceEqualityRequiredExecution.requireAll wr wh
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) request.value.children
        scanned.native.machine.heap = .done prepared preparedHeap ∧
      SourceCurrentAllocatedClassWorker.pass we wp wh wm wc wn kept prepared
        (advanceHeap scanned preparedHeap) writerMemo = .done returned.children middle writerMerge ∧
      writerSaved = scanFourth ∧
      ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches request.value.children record.paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
  obtain ⟨entry,depth,free,shape⟩ := original_shape
  have occurrence : returned.children[0]? = some original := by rw [cold_children]; rfl
  have selected := SourceCurrentOuterOwnerSelection.selected (handle := 0) warm_return
    running_inputs.1 running_ready running_origins computed_receipts.2.2.2.2.2.2.2.2.2.2
    shape (List.mem_singleton_self row) occurrence rfl
  rcases computed_receipts with ⟨top,childrenRoot,childrenChild,tauPlain,rootConstrained,field,
    coldStart,nodeEmpty,table,cell,active⟩
  exact ⟨construction,top,rfl,rfl,childrenRoot,childrenChild,tau_shape,tauPlain,rootConstrained,field,
    initial_inputs.1,initial_origins,coldStart,cold_return,cold_children,nodeEmpty,cell,began,active,
    warm_ready,warm_return,running_inputs.1,running_ready,row_list,selected⟩

/-- Actual cold publication and warm reuse retain the same selected writer and original gates. -/
theorem actual_warm_owner_selection :
    InternedFreshOrdinaryConstruction.build program [] empty = .done original initial.checked.native.machine.heap ∧
    inherited.payload = some [] ∧
    initial.nodeResults = FlatMemoThunk.empty ∧ initial.edgeResults = FlatMemoThunk.empty ∧
    children original = [child,child] ∧ children child = [tau,tau] ∧
    (∃ entry body depth ordinary, tau = .mu entry body depth ordinary) ∧
    SourceMemoGate.unconstrained tau = true ∧ SourceMemoGate.unconstrained original = false ∧
    row.entry.key.constraint = own ∧
    SourceCurrentOuterPrefixInvariants.Good initial ∧ Origins initial ∧
    (beginEdge request initial).2.1 = .evaluate request ∧
    cold = .done returned warmed ∧ returned.children = [original,child] ∧
    warmed.nodeResults = FlatMemoThunk.empty ∧
    warmed.edgeResults.cells 0 = some ⟨request,.returned returned⟩ ∧
    beginNode owner warmed = (0,.evaluate owner,running) ∧
    running.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
    beginEdge request running = (0,.ready returned,running) ∧
    warm = .done returned running ∧
    SourceCurrentOuterPrefixInvariants.Good running ∧
    SourceCurrentOuterPrefixInvariants.EdgeReady running request ∧
    nodeEdges original = [row] ∧
    Origins running ∧ original = owner.value ∧
    ∃ (wg ws wr we wp wh wm wc wn wbudget : Nat) (writerBefore writerAfter : Checked 8)
      (writerFourth writerSaved : Fourth) (writerMemo writerMerge : Memo),
      SourceCurrentAllocatedParentWorker.edge wg ws wr we wp wh wm wc wn wbudget
        request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
        request.value.children writerBefore writerFourth writerMemo =
          .done returned writerAfter writerSaved writerMerge ∧
      SourceCurrentNativeOperationHeap.Good writerBefore ∧
      SourceCurrentMemoMergeEffects.Stored writerBefore.native.machine.heap writerMemo ∧
      (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
        FieldAvailable writerBefore.operations request.value.entry.key.constraint ∧
        EqReady writerBefore.operations.constraints request.inherited ∧
        Values writerBefore.native.machine.heap request.value.children) ∧
      ∃ (loaded : Allocated) (middle : Checked 8) (records kept : List Record)
      (scanned : Checked 8) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
      SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false ∧
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint writerBefore.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce wg ws wr we wp wh wm wc wn wbudget loaded request.inherited request.value.children
        writerBefore writerFourth writerMemo = .done returned.children middle writerSaved writerMerge ∧
      SourceCurrentAllocatedMkEdge.build request.value.entry.key.symbol loaded returned.children middle = (.ok returned, writerAfter) ∧
      SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
        returned.children.length = true ∧
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard request.inherited writerBefore.operations).1 =
        .ok (.classes records) ∧
      SourceCurrentAllocatedRecordScanWorker.scan wg ws wp wh wn wbudget request.value.children records
        (prefixState writerBefore loaded request.inherited) writerFourth = .done (none, kept) scanned scanFourth ∧
      kept ≠ [] ∧
      SourceEqualityRequiredExecution.requireAll wr wh
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) request.value.children
        scanned.native.machine.heap = .done prepared preparedHeap ∧
      SourceCurrentAllocatedClassWorker.pass we wp wh wm wc wn kept prepared
        (advanceHeap scanned preparedHeap) writerMemo = .done returned.children middle writerMerge ∧
      writerSaved = scanFourth ∧
      ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches request.value.children record.paths
        scanned.native.machine.heap false scanned.native.machine.heap := checked_witness

end MicroCFTA.WarmOwnerSelectionFixture
