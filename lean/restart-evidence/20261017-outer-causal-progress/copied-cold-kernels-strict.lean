import MicroCFTA.SourceCurrentOuterCopiedCold
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.CopiedColdIntegration
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentOuterCopiedWarmHit
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

/-- The actual cold prefix completes and retains a hit at every worker bound. -/
theorem cold_prefix_then_all_fuel_hit :
    ∃ (program : InternedNestedConstruction.Syntax Symbol Guard) (input b result : Node)
      (initial cold final : Caller 8) (owner wrapper copied : NodeRequest),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input initial.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready initial.checked ∧ input.free = [] ∧
      initial.nodeResults = FlatMemoThunk.empty ∧ initial.edgeResults = FlatMemoThunk.empty ∧
      copied.value = b ∧ copied.inherited.payload = some [] ∧
      Reached 16 16 16 16 16 16 16 16 128 0 (.node 24 owner initial) (.node 18 copied cold) ∧
      cold.nodeResults.table copied.key = none ∧
      cold.nodeResults.cells 0 = some ⟨owner,.evaluating⟩ ∧
      cold.nodeResults.cells 1 = some ⟨wrapper,.evaluating⟩ ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 24 16 16 16 16 16 16 16 16 128 0 owner initial =
        .done result final ∧
      final.nodeResults.cells 2 = some ⟨copied,.returned b⟩ ∧
      ∀ fuel g s r e p h m c n budget,
        SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget copied final = .done b final := by
  obtain ⟨program,input,tau,b,initial,cold,running,afterCopy,final,result,owner,wrapper,copied,
    built,ready,_available,closed,emptyN,emptyE,_children,_plainTau,_innerGuard,_outerGuard,
    inherited,_ownerEq,copiedEq,_noOrigin,reached,_next,_rootTable,_wrapperTable,missing,
    rootActive,wrapperActive,_demand,_copiedDone,wholeDone,_finalTable,finalCell,finalDemand⟩ :=
    SourceCurrentOuterCopiedCold.copied_cold_while_owners_active
  refine ⟨program,input,b,result,initial,cold,final,owner,wrapper,copied,
    built,ready,closed,emptyN,emptyE,copiedEq,inherited,reached,missing,rootActive,wrapperActive,
    wholeDone,finalCell,?_⟩
  intro fuel g s r e p h m c n budget
  exact SourceCurrentAllocatedPartialWorker.nodeCall_ready fuel g s r e p h m c n budget
    copied final final 2 b finalDemand

end MicroCFTA.CopiedColdIntegration
