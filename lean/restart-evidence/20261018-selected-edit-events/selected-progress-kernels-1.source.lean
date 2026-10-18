import MicroCFTA.SourceCurrentOuterParentHeightGrowth
import MicroCFTA.SourceCurrentActualSharedLeafEvents
import MicroCFTA.SourceCurrentActualClassDispatch

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.SelectedProgressCheck
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
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
private def equal : Guard := ⟨some [[[0],[1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair",.top) equal [leaf,leaf]]
private def loop (name : String) : Syntax Symbol Guard := .binder false (.node [.mk (name,.top) plain [.var 0]])
private def wrapper (name : String) : Syntax Symbol Guard := .node [.mk ("wrap",.top) plain [.union [finite,loop name]]]
private def program : Syntax Symbol Guard := .node [.mk ("roots",.top) equal [wrapper "x",wrapper "y"]]
private def built := InternedFreshOrdinaryConstruction.build program [] empty
private def input : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def left : Node := (children input)[0]?.getD .empty
private def right : Node := (children input)[1]?.getD .empty
private def first := SourceEqualityConstraintAllocation.construct equal.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct plain.equalities first.2
private def equalValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def inherited : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 second.2 heap
private noncomputable def parent := SourceCurrentAllocatedParentWorker.edge 16 16 16 16 16 16 16 16 256 0
  ("roots",.top) equal inherited [left,right] before.checked before.fourth before.merge
private noncomputable def output : EdgeValue Symbol Guard := match parent with
  | .done value _ _ _ => value | _ => (run (makeEdge ("roots",.top) equal []) heap).1
private theorem computed :
    built = .done input heap ∧
    SourceCurrentAllocatedGateWorker.primary 16 [left,right] [[0],[1]] before.checked = .done false before.checked ∧
    parent = .done output parent.state parent.fourth parent.memo ∧
    MergedOrdinaryHeight.height left = 1 ∧ MergedOrdinaryHeight.height right = 1 ∧
    MergedOrdinaryHeight.edgeHeight output = 3 := by cbv
end MicroCFTA.SelectedProgressCheck
