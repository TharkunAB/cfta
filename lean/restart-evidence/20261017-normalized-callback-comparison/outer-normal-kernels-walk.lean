import MicroCFTA.SourceCurrentUnionNormalOuter
import MicroCFTA.SourceCurrentOuterEdgeIdle
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

set_option linter.all true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option pp.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.OuterNormalWalkKernels
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentOuterEdgeIdle (EdgeIdle Safe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def plain : Guard := ⟨some [], .top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("root", .top) plain [.node [.mk ("leaf", .top) plain []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def row : EdgeValue Symbol Guard :=
  ((nodeEdges root)[0]?).getD (run (makeEdge ("root", .top) plain []) heap).1
private def inherited := SourceCurrentAllocatedPartialInitialization.emptyValue Cache.emptyState
private def cold := SourceCurrentAllocatedPartialInitialization.caller 8 Cache.emptyState heap
private def ancestor : NodeRequest := ⟨.contradiction,.empty⟩
private def before := (beginNode ancestor cold).2.2
private def request : NodeRequest := ⟨inherited,root⟩
private noncomputable def actual := SourceCurrentAllocatedPartialWorker.nodeCall 8 4 4 4 4 4 4 4 4 32 0 request before
private noncomputable def after := actual.state
private theorem built_done : built = .done root heap := by cbv
private theorem facts : InternedNestedFacts.Facts heap := (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem before_idle : EdgeIdle before :=
  SourceCurrentOuterEdgeIdle.initial cold.checked cold.merge cold.fourth
private theorem actual_done : actual = .done root after := by cbv


/-- Own nonempty outer traversal retains normality beside an evaluating ancestor, then reuses the exact warm node and edge cells. -/
theorem constructed_walk_warm_required :
    built = .done root heap ∧ Available heap root ∧ row.children.length = 1 ∧
    before.nodeResults.cells 0 = some ⟨ancestor,.evaluating⟩ ∧
    SourceCurrentAllocatedPartialWorker.nodeCall 8 4 4 4 4 4 4 4 4 32 0 request before = .done root after ∧
    SourceCurrentRequiredUnionNormal.UnionNormal after.checked.native.machine.heap ∧
    after.nodeResults.cells 0 = some ⟨ancestor,.evaluating⟩ ∧
    SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request after = .done root after ∧
    SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 ⟨inherited,row⟩ after = .done row after ∧
    ∀ worker reader, SourceCurrentRequiredUnionNormalRead.StoppedNormal
      (SourceEqualityRequiredExecution.requireAll worker reader [[0,0]] [root,.reference .depth] after.checked.native.machine.heap) := by
  have initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap :=
    SourceCurrentRequiredUnionNormal.source expression
  have normal := SourceCurrentUnionNormalOuter.node_call 8 4 4 4 4 4 4 4 4 32 0 request before initialNormal
  change SourceCurrentRequiredUnionNormal.UnionNormal actual.state.checked.native.machine.heap at normal
  rw [actual_done] at normal
  refine ⟨built_done,available,?_,?_,actual_done,normal,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · intro worker reader
    exact SourceCurrentRequiredUnionNormalRead.requireAll worker reader [[0,0]] _ _ normal
end MicroCFTA.OuterNormalWalkKernels
