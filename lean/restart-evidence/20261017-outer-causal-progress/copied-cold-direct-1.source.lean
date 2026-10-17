import MicroCFTA.SourceCurrentOuterCopiedWarmHit
import MicroCFTA.SourceCurrentRequiredRowOrigins
import MicroCFTA.SourceCurrentGatePlainRegion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

/-!
# A copied constrained child can be cold before its source sibling

The actual source has a plain recursive branch before the finite constrained
branch. Its parent equality copies the finite branch into the first returned
wrapper. The literal outer prefix reaches that copy before the source sibling.
The copy starts a fresh owner while both enclosing owners remain active.
This finite execution does not establish a general progress order.
-/
namespace MicroCFTA.SourceCurrentOuterCopiedCold

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


open SourceCurrentOuterCopiedWarmHit (Phase Step Reached)
private def plain : Guard := ⟨some [], .top⟩
private def inner : Guard := ⟨some [[[0], [1]]], .top⟩
private def outer : Guard := ⟨some [[[0, 0], [1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair", .top) inner [leaf, leaf]]
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf", .top) plain [], .mk ("pair", .top) plain [.var 0, .var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) outer [recursive, finite]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def b := ((children original)[1]?).getD (Value.empty : Value Symbol Guard)
private def tau := ((children original)[0]?).getD (Value.empty : Value Symbol Guard)
private def first := SourceEqualityConstraintAllocation.construct outer.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct inner.equalities first.2
private def third := SourceEqualityConstraintAllocation.construct plain.equalities second.2
private def outerValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def innerValue : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def plainValue : SourceEqualityConstraintAllocation.Value := match third.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 third.2 heap
private def sourceEdge : EdgeValue Symbol Guard :=
  ((nodeEdges original)[0]?).getD (run (makeEdge ("roots", .top) outer [tau,b]) heap).1

private theorem cached_inner : SourceEqualityGuardReadback.Cached inner.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem cached_outer : SourceEqualityGuardReadback.Cached outer.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0, 0], [1]]] = .normalized [[[0, 0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState third.2 [outer,inner,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [outer] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_outer (show first = (.ok outerValue,first.2) by cbv)
  have two : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [outer,inner] :=
    SourceEqualityOriginalAllocationHistory.History.construct one cached_inner (show second = (.ok innerValue,second.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct two SourceEqualityGuardReadback.empty_cached
    (show third = (.ok plainValue,third.2) by cbv)
private theorem built_done : built = .done original heap := by cbv
private theorem source_ready : SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧ original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original := by
  have initial := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid expression
    (fun guard member => by
      simp only [expression,finite,leaf,recursive,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) original heap built_done
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ initial.1.good.operations
  exact ⟨⟨⟨initial.1.good.native,initial.1.good.heap,allocated.1,initial.1.good.fields.grows allocated.2.1⟩,
    initial.1.semantic,initial.1.costs,initial.1.scopedCache,initial.1.idle⟩,initial.2⟩


private def rootRequest : NodeRequest := ⟨plainValue,original⟩
private def rootRunning := (beginNode rootRequest before).2.2
private noncomputable def rootEdgeCall := SourceCurrentAllocatedPartialWorker.edgeCall
  22 16 16 16 16 16 16 16 16 128 0 ⟨plainValue,sourceEdge⟩ rootRunning
private noncomputable def narrowed : Edge := match rootEdgeCall with
  | .done value _ => value | .failed .. => sourceEdge
private noncomputable def rootAfter := rootEdgeCall.state
private noncomputable def rootCombined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run narrowed.entry.key.constraint plainValue rootAfter.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def rootPrefix := SourceCurrentAllocatedPartialGraph.prefixState rootAfter narrowed plainValue
private noncomputable def firstDescent := SourceCurrentAllocatedPartialGraph.descend rootPrefix rootCombined 0
private noncomputable def wrapper : Node := (narrowed.children[0]?).getD .empty
private noncomputable def wrapperRequest : NodeRequest := ⟨firstDescent.1,wrapper⟩
private noncomputable def wrapperRunning := (beginNode wrapperRequest firstDescent.2).2.2
private noncomputable def wrapperEdge : Edge := (nodeEdges wrapper)[0]?.getD sourceEdge
private noncomputable def wrapperEdgeCall := SourceCurrentAllocatedPartialWorker.edgeCall
  19 16 16 16 16 16 16 16 16 128 0 ⟨wrapperRequest.inherited,wrapperEdge⟩ wrapperRunning
private noncomputable def wrapperNarrowed : Edge := match wrapperEdgeCall with
  | .done value _ => value | .failed .. => wrapperEdge
private noncomputable def wrapperAfter := wrapperEdgeCall.state
private noncomputable def innerCombined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run wrapperNarrowed.entry.key.constraint wrapperRequest.inherited wrapperAfter.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def innerPrefix := SourceCurrentAllocatedPartialGraph.prefixState wrapperAfter wrapperNarrowed wrapperRequest.inherited
private noncomputable def copied : Node := (wrapperNarrowed.children[0]?).getD .empty
private noncomputable def copiedDescent := SourceCurrentAllocatedPartialGraph.descend innerPrefix innerCombined 0
private noncomputable def copiedRequest : NodeRequest := ⟨copiedDescent.1,copied⟩
private noncomputable def atCopied := copiedDescent.2
private noncomputable def copiedRunning := (beginNode copiedRequest atCopied).2.2
private noncomputable def copiedCall := SourceCurrentAllocatedPartialWorker.nodeCall
  18 16 16 16 16 16 16 16 16 128 0 copiedRequest atCopied
private theorem actual_facts :
    beginNode rootRequest before = (0,.evaluate rootRequest,rootRunning) ∧
    nodeEdges original = [sourceEdge] ∧
    rootEdgeCall = .done narrowed rootAfter ∧ rootCombined = outerValue ∧
    narrowed.children = [wrapper,b] ∧
    beginNode wrapperRequest firstDescent.2 = (1,.evaluate wrapperRequest,wrapperRunning) ∧
    nodeEdges wrapper = [wrapperEdge] ∧ wrapperEdgeCall = .done wrapperNarrowed wrapperAfter ∧
    innerCombined = plainValue ∧ wrapperNarrowed.children = [copied,tau] ∧ copied = b ∧
    copiedRequest.inherited = plainValue ∧ atCopied.nodeResults.table copiedRequest.key = none ∧
    atCopied.nodeResults.cells 0 = some ⟨rootRequest,.evaluating⟩ ∧
    atCopied.nodeResults.cells 1 = some ⟨wrapperRequest,.evaluating⟩ ∧
    beginNode copiedRequest atCopied = (2,.evaluate copiedRequest,copiedRunning) ∧
    copiedCall = .done b copiedCall.state := by cbv


private theorem ordinary_shape (value : Node)
    (ordinary : (match value with | .node .. => true | _ => false) = true) :
    ∃ entry depth free, value = .node entry (nodeEdges value) depth free := by
  cases value <;> simp_all [nodeEdges]
private theorem original_shape : ∃ entry depth free, original = .node entry [sourceEdge] depth free := by
  obtain ⟨entry, depth, free, shape⟩ := ordinary_shape original (by cbv)
  have rows : nodeEdges original = [sourceEdge] := by cbv
  exact ⟨entry,depth,free,by simpa only [rows] using shape⟩
private theorem wrapper_shape : ∃ entry depth free, wrapper = .node entry [wrapperEdge] depth free := by
  obtain ⟨entry, depth, free, shape⟩ := ordinary_shape wrapper (by cbv)
  have rows : nodeEdges wrapper = [wrapperEdge] := by cbv
  exact ⟨entry,depth,free,by simpa only [rows] using shape⟩
private theorem reached : Reached 16 16 16 16 16 16 16 16 128 0
    (.node 24 rootRequest before) (.node 18 copiedRequest atCopied) := by
  obtain ⟨entry,depth,free,shape⟩ := original_shape
  obtain ⟨wrapperEntry,wrapperDepth,wrapperFree,wrapperShape⟩ := wrapper_shape
  rcases actual_facts with ⟨started,_originalRows,rootDone,rootLive,rootChildren,
    wrapperStarted,_wrapperRows,wrapperDone,innerLive,wrapperChildren,_copied,
    _inherited,_missing,_rootActive,_wrapperActive,_copyStarted,_copyDone⟩
  have rootPrefixDone : (SourceCurrentAllocatedInheritedPrefix.run narrowed.entry.key.constraint plainValue
      rootAfter.checked.operations).1 = .ok (some outerValue) := by cbv
  have innerPrefixDone : (SourceCurrentAllocatedInheritedPrefix.run wrapperNarrowed.entry.key.constraint
      wrapperRequest.inherited wrapperAfter.checked.operations).1 = .ok (some plainValue) := by cbv
  refine .step (.node_evaluate started) (.step (.body_rows shape) ?_)
  refine .step (.rows_edge rootDone) (.step (.descendants_children rootPrefixDone) ?_)
  refine .step (.children_walk (by cbv; intro impossible; cases impossible)) ?_
  rw [← rootLive,rootChildren]
  refine .step .walk_head (.step (.node_evaluate wrapperStarted) ?_)
  refine .step (.body_rows wrapperShape) (.step (.rows_edge wrapperDone) ?_)
  refine .step (.descendants_children innerPrefixDone) ?_
  refine .step (.children_walk (by cbv; intro impossible; cases impossible)) ?_
  rw [← innerLive,wrapperChildren]
  exact .step .walk_head .refl
private theorem tau_only_impossible : ¬ SourceCurrentRequiredRowOrigins.Origin tau copied := by
  have available : Available heap tau := source_ready.2.1.children tau
    (List.mem_of_getElem? (show (children original)[0]? = some tau by cbv))
  have coherent := (InternedFreshOrdinaryFacts.closed_verified expression).facts.coherent
  have annotated := SourceCurrentGatePlainRegion.annotations heap tau coherent available (by cbv)
  have rows : nodeEdges copied ≠ [] := by cbv; intro impossible; cases impossible
  cases selected : nodeEdges copied with
  | nil => exact False.elim (rows selected)
  | cons row rest =>
      have nonplain : SourceMemoGate.plain row.entry.key.constraint = false := by
        have guards : (nodeEdges copied).map (fun edge => SourceMemoGate.plain edge.entry.key.constraint) = [false] := by cbv
        rw [selected] at guards
        exact (List.cons.inj guards).1
      intro origin
      obtain ⟨path,index,sourceRow,occurrence,fields⟩ := origin.nonplain
        (SourceCurrentRequiredRowOrigins.RowAt.root (by rw [selected]; rfl)) nonplain
      have plain := occurrence.annotated annotated
      have guard := fields.2.1
      rw [guard,nonplain] at plain
      cases plain
private noncomputable def fullCall := SourceCurrentAllocatedPartialWorker.nodeCall
  24 16 16 16 16 16 16 16 16 128 0 rootRequest before
private noncomputable def output : Node := match fullCall with
  | .done result _ => result | .failed .. => .empty
private theorem final_facts :
    fullCall = .done output fullCall.state ∧
    fullCall.state.nodeResults.table copiedRequest.key = some 2 ∧
    fullCall.state.nodeResults.cells 2 = some ⟨copiedRequest,.returned b⟩ ∧
    beginNode copiedRequest fullCall.state = (2,.ready b,fullCall.state) := by cbv

/-- Actual initial source execution reaches a cold copied child, then completes and retains its warm result. -/
theorem copied_cold_while_owners_active :
    ∃ (program : Syntax Symbol Guard) (input recursiveValue finiteValue : Node)
      (initial cold running final : Caller 8) (result : Node)
      (owner wrapperOwner copiedOwner : NodeRequest),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input initial.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready initial.checked ∧
      Available initial.checked.native.machine.heap input ∧ input.free = [] ∧
      initial.nodeResults = FlatMemoThunk.empty ∧ initial.edgeResults = FlatMemoThunk.empty ∧
      children input = [recursiveValue,finiteValue] ∧
      SourceMemoGate.unconstrained recursiveValue = true ∧
      (nodeEdges finiteValue).map (fun row => row.entry.key.constraint) = [⟨some [[[0],[1]]],.top⟩] ∧
      owner.value = input ∧ copiedOwner.value = finiteValue ∧
      ¬ SourceCurrentRequiredRowOrigins.Origin recursiveValue copiedOwner.value ∧
      Reached 16 16 16 16 16 16 16 16 128 0 (.node 24 owner initial) (.node 18 copiedOwner cold) ∧
      cold.nodeResults.next = 2 ∧ cold.nodeResults.table owner.key = some 0 ∧
      cold.nodeResults.table wrapperOwner.key = some 1 ∧ cold.nodeResults.table copiedOwner.key = none ∧
      cold.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
      cold.nodeResults.cells 1 = some ⟨wrapperOwner,.evaluating⟩ ∧
      beginNode copiedOwner cold = (2,.evaluate copiedOwner,running) ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 18 16 16 16 16 16 16 16 16 128 0 copiedOwner cold =
        .done finiteValue copiedCall.state ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 24 16 16 16 16 16 16 16 16 128 0 owner initial = .done result final ∧
      final.nodeResults.table copiedOwner.key = some 2 ∧
      final.nodeResults.cells 2 = some ⟨copiedOwner,.returned finiteValue⟩ ∧
      beginNode copiedOwner final = (2,.ready finiteValue,final) := by
  refine ⟨expression,original,tau,b,before,atCopied,copiedRunning,fullCall.state,output,
    rootRequest,wrapperRequest,copiedRequest,built_done,source_ready.1,source_ready.2.1,
    source_ready.2.2.1,rfl,rfl,?_,?_,?_,rfl,?_,tau_only_impossible,reached,?_,?_,?_,?_,?_,?_,?_,?_,
    final_facts.1,final_facts.2.1,final_facts.2.2.1,final_facts.2.2.2⟩
  all_goals
    first
    | exact actual_facts.2.2.2.2.2.2.2.2.2.2.2.1
    | cbv
end MicroCFTA.SourceCurrentOuterCopiedCold
