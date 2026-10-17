import MicroCFTA.SourceCurrentOuterCopiedWarmHit
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.OuterCopiedColdExploration

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
end MicroCFTA.OuterCopiedColdExploration
