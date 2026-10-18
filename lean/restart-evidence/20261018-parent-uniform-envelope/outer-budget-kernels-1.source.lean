import MicroCFTA.SourceCurrentOuterCallBudget
import MicroCFTA.SourceEqualityPCSNativeEdge
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.OuterBudgetKernels
noncomputable section
open Cache InternedConstructorTemplates
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq FullSyntax.Formula := fun first second =>
  decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private def rejected : Guard := ⟨none,.top⟩
private def expression : Syntax Symbol Guard := .node [
  .mk ("first",.top) rejected [],.mk ("second",.top) rejected []]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def checked : SourceEqualityNativeDemand.State 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩, SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩
private def caller := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨.contradiction,root⟩
private def full := SourceCurrentOuterCallBudget.node 3 0 0 0 0 0 0 0 0 0 0 request caller
private def short := SourceCurrentOuterCallBudget.node 2 0 0 0 0 0 0 0 0 0 0 request caller
private def returned : Value Symbol Guard := match full.outcome with | .done value _ => value | _ => .empty
private def after := full.outcome.state
private def warm := SourceCurrentOuterCallBudget.node 0 0 0 0 0 0 0 0 0 0 0 request after

private theorem full_done : full.outcome = .done returned after := by
  have tag : (match full.outcome with | .done .. => true | _ => false) = true := by cbv
  cases observed : full.outcome <;> simp_all only [returned,after,SourceCurrentAllocatedPartialWorker.Outcome.state,Bool.false_eq_true]
private theorem witness :
    built = .done root heap ∧
    full.outcome = SourceCurrentAllocatedPartialWorker.nodeCall 3 0 0 0 0 0 0 0 0 0 0 request caller ∧
    full.outcome = .done returned after ∧ full.calls.length = 2 ∧
    full.calls[0]?.map (fun site => site.1.value.entry.key.symbol) = some ("first",.top) ∧
    full.calls[1]?.map (fun site => site.1.value.entry.key.symbol) = some ("second",.top) ∧
    (∃ stopped, short.outcome = .failed (.exhausted .rows) stopped) ∧ short.calls.length = 1 ∧
    warm.outcome = .done returned after ∧ warm.calls = [] ∧
    full.calls.length ≤ SourceCurrentOuterCallBudget.budget 3 ∧
    short.calls.length ≤ SourceCurrentOuterCallBudget.budget 2 := by
  refine ⟨?_,(SourceCurrentOuterCallBudget.node_budget 3 0 0 0 0 0 0 0 0 0 0 request caller).1,
    full_done,?_,?_,?_,?_,?_,?_,?_,
    (SourceCurrentOuterCallBudget.node_budget 3 0 0 0 0 0 0 0 0 0 0 request caller).2,
    (SourceCurrentOuterCallBudget.node_budget 2 0 0 0 0 0 0 0 0 0 0 request caller).2⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · have tag : (match short.outcome with | .failed (.exhausted .rows) _ => true | _ => false) = true := by cbv
    cases observed : short.outcome <;> simp_all only
    rename_i fault stopped
    cases fault <;> simp_all only
    rename_i phase
    cases phase <;> simp_all only
    exact ⟨stopped,rfl⟩
  · cbv
  · cbv
  · cbv

/-- Two actual Parent sites, an exhausted prefix, and a warm hit obey the same fuel-only budget. -/
theorem ordered_sites_and_stopping_prefix :
    built = .done root heap ∧
    full.outcome = SourceCurrentAllocatedPartialWorker.nodeCall 3 0 0 0 0 0 0 0 0 0 0 request caller ∧
    full.outcome = .done returned after ∧ full.calls.length = 2 ∧
    full.calls[0]?.map (fun site => site.1.value.entry.key.symbol) = some ("first",.top) ∧
    full.calls[1]?.map (fun site => site.1.value.entry.key.symbol) = some ("second",.top) ∧
    (∃ stopped, short.outcome = .failed (.exhausted .rows) stopped) ∧ short.calls.length = 1 ∧
    warm.outcome = .done returned after ∧ warm.calls = [] ∧
    full.calls.length ≤ SourceCurrentOuterCallBudget.budget 3 ∧
    short.calls.length ≤ SourceCurrentOuterCallBudget.budget 2 := witness
end
end MicroCFTA.OuterBudgetKernels
