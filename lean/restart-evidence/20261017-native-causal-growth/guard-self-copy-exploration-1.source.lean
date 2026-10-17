import MicroCFTA.SourceCurrentOuterCopiedWarmHit
import MicroCFTA.SourceCurrentRequiredRowOrigins
import MicroCFTA.SourceCurrentGatePlainRegion
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000


namespace MicroCFTA.GuardSelfCopyExploration

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

theorem actual_parent :
    built = .done original heap ∧
    inherited.payload = some [] ∧
    parent = .done returned parent.state ∧
    returned.children = [original,child] := by cbv
end MicroCFTA.GuardSelfCopyExploration
