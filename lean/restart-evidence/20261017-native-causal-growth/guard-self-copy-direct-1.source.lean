import MicroCFTA.SourceCurrentOuterCopiedWarmHit
/-!
# An original constrained value can repeat with a new inherited key

The actual parent copies the original root below itself. Its earlier owner
remains evaluating. The repeated request has a distinct inherited key.
Its actual local precheck erases the children, and the complete root call
returns Empty. This finite witness refutes strict physical-source descent.
It does not establish a busy-key recurrence or a failure of termination.
-/
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000


namespace MicroCFTA.SourceCurrentOuterOriginalRepeat

open Cache InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionKernel InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

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
private def inherited : EqValue := match second.1 with | .ok value => value | _ => .contradiction
private def initial := SourceCurrentAllocatedPartialInitialization.caller 8 second.2 heap
private def owner : NodeRequest := ⟨inherited,original⟩
private def running := (beginNode owner initial).2.2
private def edge : Edge := (nodeEdges original)[0]?.getD (run (makeEdge ("pair",.top) own [child,child]) heap).1
private noncomputable def parent := SourceCurrentAllocatedPartialWorker.edgeCall
  22 16 16 16 16 16 16 16 16 256 0 ⟨inherited,edge⟩ running
private noncomputable def returned : Edge := match parent with | .done value _ => value | .failed .. => edge

private theorem actual_parent :
    built = .done original heap ∧
    inherited.payload = some [] ∧
    parent = .done returned parent.state ∧
    returned.children = [original,child] := by cbv

private def ownValue : EqValue := match first.1 with | .ok value => value | _ => .contradiction
private theorem cached_own : SourceEqualityGuardReadback.Cached own.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0,0],[0,1],[1]]] = .normalized [[[0,0],[0,1],[1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [own,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [own] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_own (show first = (.ok ownValue,first.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct one SourceEqualityGuardReadback.empty_cached
    (show second = (.ok inherited,second.2) by cbv)
private theorem initial_ready : SourceCurrentConjunctionClassScan.Ready initial.checked ∧
    Available heap original ∧ original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original := by
  have entry := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid program
    (fun guard member => by
      simp only [program,cPlan,tauPlan,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    original heap actual_parent.1
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ entry.1.good.operations
  exact ⟨⟨⟨entry.1.good.native,entry.1.good.heap,allocated.1,entry.1.good.fields.grows allocated.2.1⟩,
    entry.1.semantic,entry.1.costs,entry.1.scopedCache,entry.1.idle⟩,entry.2⟩

private noncomputable def combined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint inherited parent.state.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def prefixState := SourceCurrentAllocatedPartialGraph.prefixState parent.state returned inherited
private noncomputable def descended := SourceCurrentAllocatedPartialGraph.descend prefixState combined 0
private noncomputable def repeated : NodeRequest := ⟨descended.1,(returned.children[0]?).getD .empty⟩
private noncomputable def repeatedRunning := (beginNode repeated descended.2).2.2
private noncomputable def nextPrefix := SourceCurrentAllocatedInheritedPrefix.run own repeated.inherited descended.2.checked.operations
private noncomputable def repeatedCall := SourceCurrentAllocatedPartialWorker.nodeCall
  21 16 16 16 16 16 16 16 16 256 0 repeated descended.2
private noncomputable def fullCall := SourceCurrentAllocatedPartialWorker.nodeCall
  24 16 16 16 16 16 16 16 16 256 0 owner initial

private theorem key_different : repeated.key ≠ owner.key := by
  have left : repeated.key.1 = some 2 := by cbv
  have right : owner.key.1 = some 1 := by cbv
  intro same
  have identities := congrArg Prod.fst same
  rw [left,right] at identities
  cases identities

private theorem actual_phase :
    SourceCurrentConjunctionClassScan.Ready initial.checked ∧ Available heap original ∧ original.free = [] ∧
    SourceMemoGate.unconstrained original = false ∧
    repeated.value = original ∧ SourceEqualityInheritedPayload.classes repeated.inherited.payload = some [[[0],[1]]] ∧
    repeated.key ≠ owner.key ∧
    descended.2.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
    descended.2.nodeResults.table repeated.key = none ∧
    beginNode repeated descended.2 = (1,.evaluate repeated,repeatedRunning) ∧
    nextPrefix.1 = .ok (some .contradiction) ∧
    repeatedCall = .done .empty repeatedCall.state ∧
    fullCall = .done .empty fullCall.state := by
  refine ⟨initial_ready.1,initial_ready.2.1,initial_ready.2.2.1,?_,?_,?_,key_different,?_,?_,?_,?_,?_,?_⟩
  all_goals cbv

open SourceCurrentOuterCopiedWarmHit (Phase Step Reached)
private theorem ordinary_shape (value : Node)
    (ordinary : (match value with | .node .. => true | _ => false) = true) :
    ∃ entry depth free, value = .node entry (nodeEdges value) depth free := by
  cases value <;> simp_all [nodeEdges]
private theorem original_shape : ∃ entry depth free, original = .node entry [edge] depth free := by
  obtain ⟨entry,depth,free,shape⟩ := ordinary_shape original (by cbv)
  have rows : nodeEdges original = [edge] := by cbv
  exact ⟨entry,depth,free,by simpa only [rows] using shape⟩

private theorem actual_reached : Reached 16 16 16 16 16 16 16 16 256 0
    (.node 24 owner initial) (.node 21 repeated descended.2) := by
  obtain ⟨entry,depth,free,shape⟩ := original_shape
  have started : beginNode owner initial = (0,.evaluate owner,running) := by cbv
  have prefixDone : (SourceCurrentAllocatedInheritedPrefix.run returned.entry.key.constraint inherited
      parent.state.checked.operations).1 = .ok (some combined) := by cbv
  refine .step (.node_evaluate started) (.step (.body_rows shape) ?_)
  refine .step (.rows_edge actual_parent.2.2.1) (.step (.descendants_children prefixDone) ?_)
  refine .step (.children_walk (by cbv; intro impossible; cases impossible)) ?_
  unfold repeated
  rw [actual_parent.2.2.2]
  exact .step .walk_head .refl

private noncomputable def loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula :=
  match SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint repeatedRunning.checked.operations.constraints with
  | .ok (some value) => value | _ => ⟨.contradiction,.top⟩
private noncomputable def precheck := SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard
  repeated.inherited repeatedRunning.checked.operations

private theorem actual_precheck :
    SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint repeatedRunning.checked.operations.constraints = .ok (some loaded) ∧
    precheck.1 = .ok .emptyChildren ∧
    beginNode repeated fullCall.state = (1,.ready .empty,fullCall.state) := by cbv

private theorem witness :
    ∃ (expression : Syntax Symbol Guard) (input c recursiveValue : Node)
      (before entered afterParent atRepeated running afterRepeated final : Caller 8)
      (root repeatedRequest : NodeRequest) (sourceRow parented : Edge)
      (field : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input before.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready before.checked ∧
      Available before.checked.native.machine.heap input ∧ input.free = [] ∧
      SourceRecursiveIntersectionInputView.Original input ∧
      before.nodeResults = FlatMemoThunk.empty ∧ before.edgeResults = FlatMemoThunk.empty ∧
      children input = [c,c] ∧ children c = [recursiveValue,recursiveValue] ∧
      SourceMemoGate.unconstrained recursiveValue = true ∧ SourceMemoGate.unconstrained input = false ∧
      (nodeEdges input).map (fun row => row.entry.key.constraint) = [⟨some [[[0,0],[0,1],[1]]],.top⟩] ∧
      (nodeEdges c).map (fun row => row.entry.key.constraint) = [⟨some [[[0,0],[0,1],[1]]],.top⟩] ∧
      root.value = input ∧ root.inherited.payload = some [] ∧ nodeEdges input = [sourceRow] ∧
      beginNode root before = (0,.evaluate root,entered) ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 22 16 16 16 16 16 16 16 16 256 0
        ⟨root.inherited,sourceRow⟩ entered = .done parented afterParent ∧
      parented.children = [input,c] ∧
      Reached 16 16 16 16 16 16 16 16 256 0 (.node 24 root before) (.node 21 repeatedRequest atRepeated) ∧
      repeatedRequest.value = input ∧
      SourceEqualityInheritedPayload.classes repeatedRequest.inherited.payload = some [[[0],[1]]] ∧
      repeatedRequest.key ≠ root.key ∧
      atRepeated.nodeResults.table root.key = some 0 ∧
      atRepeated.nodeResults.cells 0 = some ⟨root,.evaluating⟩ ∧
      atRepeated.nodeResults.table repeatedRequest.key = none ∧
      beginNode repeatedRequest atRepeated = (1,.evaluate repeatedRequest,running) ∧
      SourceEqualityConstraintFieldLookup.load sourceRow.entry.key.constraint running.checked.operations.constraints = .ok (some field) ∧
      (SourceEqualityPartialPrecheckAllocation.run field.stored field.guard repeatedRequest.inherited
        running.checked.operations).1 = .ok .emptyChildren ∧
      (SourceCurrentAllocatedInheritedPrefix.run sourceRow.entry.key.constraint repeatedRequest.inherited
        atRepeated.checked.operations).1 = .ok (some .contradiction) ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 21 16 16 16 16 16 16 16 16 256 0 repeatedRequest atRepeated =
        .done .empty afterRepeated ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 24 16 16 16 16 16 16 16 16 256 0 root before = .done .empty final ∧
      final.nodeResults.cells 0 = some ⟨root,.returned .empty⟩ ∧
      final.nodeResults.cells 1 = some ⟨repeatedRequest,.returned .empty⟩ ∧
      beginNode repeatedRequest final = (1,.ready .empty,final) := by
  rcases actual_parent with ⟨built,top,parentDone,parentChildren⟩
  rcases actual_phase with ⟨ready,available,closed,nonplain,same,inheritedChanged,different,
    active,missing,demand,contradiction,childDone,fullDone⟩
  rcases actual_precheck with ⟨fieldFound,checked,warm⟩
  refine ⟨program,original,child,tau,initial,running,parent.state,descended.2,repeatedRunning,
    repeatedCall.state,fullCall.state,owner,repeated,edge,returned,loaded,
    built,ready,available,closed,initial_ready.2.2.2,rfl,rfl,?_,?_,?_,nonplain,?_,?_,rfl,top,?_,?_,
    parentDone,parentChildren,actual_reached,same,inheritedChanged,different,?_,active,missing,demand,
    fieldFound,checked,contradiction,childDone,fullDone,?_,?_,warm⟩
  all_goals cbv

/-- The same original value is reached under a new inherited key before its owner returns. -/
theorem original_reappears_with_new_inherited :
    ∃ (expression : Syntax Symbol Guard) (input c recursiveValue : Node)
      (before entered afterParent atRepeated running afterRepeated final : Caller 8)
      (root repeatedRequest : NodeRequest) (sourceRow parented : Edge)
      (field : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input before.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready before.checked ∧
      Available before.checked.native.machine.heap input ∧ input.free = [] ∧
      SourceRecursiveIntersectionInputView.Original input ∧
      before.nodeResults = FlatMemoThunk.empty ∧ before.edgeResults = FlatMemoThunk.empty ∧
      children input = [c,c] ∧ children c = [recursiveValue,recursiveValue] ∧
      SourceMemoGate.unconstrained recursiveValue = true ∧ SourceMemoGate.unconstrained input = false ∧
      (nodeEdges input).map (fun row => row.entry.key.constraint) = [⟨some [[[0,0],[0,1],[1]]],.top⟩] ∧
      (nodeEdges c).map (fun row => row.entry.key.constraint) = [⟨some [[[0,0],[0,1],[1]]],.top⟩] ∧
      root.value = input ∧ root.inherited.payload = some [] ∧ nodeEdges input = [sourceRow] ∧
      beginNode root before = (0,.evaluate root,entered) ∧
      SourceCurrentAllocatedPartialWorker.edgeCall 22 16 16 16 16 16 16 16 16 256 0
        ⟨root.inherited,sourceRow⟩ entered = .done parented afterParent ∧
      parented.children = [input,c] ∧
      Reached 16 16 16 16 16 16 16 16 256 0 (.node 24 root before) (.node 21 repeatedRequest atRepeated) ∧
      repeatedRequest.value = input ∧
      SourceEqualityInheritedPayload.classes repeatedRequest.inherited.payload = some [[[0],[1]]] ∧
      repeatedRequest.key ≠ root.key ∧
      atRepeated.nodeResults.table root.key = some 0 ∧
      atRepeated.nodeResults.cells 0 = some ⟨root,.evaluating⟩ ∧
      atRepeated.nodeResults.table repeatedRequest.key = none ∧
      beginNode repeatedRequest atRepeated = (1,.evaluate repeatedRequest,running) ∧
      SourceEqualityConstraintFieldLookup.load sourceRow.entry.key.constraint running.checked.operations.constraints = .ok (some field) ∧
      (SourceEqualityPartialPrecheckAllocation.run field.stored field.guard repeatedRequest.inherited
        running.checked.operations).1 = .ok .emptyChildren ∧
      (SourceCurrentAllocatedInheritedPrefix.run sourceRow.entry.key.constraint repeatedRequest.inherited
        atRepeated.checked.operations).1 = .ok (some .contradiction) ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 21 16 16 16 16 16 16 16 16 256 0 repeatedRequest atRepeated =
        .done .empty afterRepeated ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 24 16 16 16 16 16 16 16 16 256 0 root before = .done .empty final ∧
      final.nodeResults.cells 0 = some ⟨root,.returned .empty⟩ ∧
      final.nodeResults.cells 1 = some ⟨repeatedRequest,.returned .empty⟩ ∧
      beginNode repeatedRequest final = (1,.ready .empty,final) := witness

end MicroCFTA.SourceCurrentOuterOriginalRepeat
