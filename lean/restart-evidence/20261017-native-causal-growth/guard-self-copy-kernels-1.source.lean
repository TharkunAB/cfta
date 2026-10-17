import MicroCFTA.SourceCurrentOuterOriginalRepeat
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
namespace MicroCFTA.OriginalRepeatIntegration
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentOuterCopiedWarmHit (Reached)
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

/-- The repeated original value uses a larger incoming path height, completes, and retains a hit at every fuel. -/
theorem original_repeat_all_fuels :
    ∃ (program : InternedNestedConstruction.Syntax Symbol Guard) (input : Node)
      (before atRepeated final : Caller 8) (root repeated : NodeRequest),
      InternedFreshOrdinaryConstruction.build program [] empty = .done input before.checked.native.machine.heap ∧
      SourceCurrentConjunctionClassScan.Ready before.checked ∧
      Available before.checked.native.machine.heap input ∧ input.free = [] ∧
      SourceMemoGate.unconstrained input = false ∧
      Reached 16 16 16 16 16 16 16 16 256 0 (.node 24 root before) (.node 21 repeated atRepeated) ∧
      root.value = input ∧ repeated.value = input ∧ repeated.key ≠ root.key ∧
      atRepeated.nodeResults.cells 0 = some ⟨root,.evaluating⟩ ∧
      EqualityModel.depth ((SourceEqualityInheritedPayload.classes root.inherited.payload).getD []).flatten = 0 ∧
      EqualityModel.depth ((SourceEqualityInheritedPayload.classes repeated.inherited.payload).getD []).flatten = 1 ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 24 16 16 16 16 16 16 16 16 256 0 root before = .done .empty final ∧
      ∀ fuel g s r e p h m c n budget,
        SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget repeated final = .done .empty final := by
  obtain ⟨program,input,c,tau,before,entered,afterParent,atRepeated,running,afterRepeated,final,
    root,repeated,sourceRow,parented,field,built,ready,available,closed,_original,_emptyN,_emptyE,
    _children,_cChildren,_plainTau,nonplain,_guardB,_guardC,rootEq,top,_rows,_rootDemand,
    _parentDone,_parentChildren,reached,repeatedEq,inherited,different,_tableRoot,activeRoot,
    _missing,_repeatDemand,_loaded,_precheck,_contradiction,_childDone,fullDone,_rootReturned,
    _childReturned,warm⟩ := SourceCurrentOuterOriginalRepeat.original_reappears_with_new_inherited
  refine ⟨program,input,before,atRepeated,final,root,repeated,built,ready,available,closed,
    nonplain,reached,rootEq,repeatedEq,different,activeRoot,?_,?_,fullDone,?_⟩
  · rw [top]; rfl
  · rw [inherited]; rfl
  · intro fuel g s r e p h m c n budget
    exact SourceCurrentAllocatedPartialWorker.nodeCall_ready fuel g s r e p h m c n budget
      repeated final final 1 .empty warm
end MicroCFTA.OriginalRepeatIntegration
#check @MicroCFTA.OriginalRepeatIntegration.original_repeat_all_fuels
#print axioms MicroCFTA.OriginalRepeatIntegration.original_repeat_all_fuels
