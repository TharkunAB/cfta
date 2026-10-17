import MicroCFTA.SourceCurrentOuterBusyOwners
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000
namespace MicroCFTA.BusyOwnerKernels
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def edgeBuilt := run (makeEdge (("leaf",.top) : Symbol) (⟨some [],.top⟩ : Guard) []) empty
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 Cache.emptyState edgeBuilt.2
private def nodeRequest : NodeRequest := ⟨.contradiction,.empty⟩
private def edgeRequest : EdgeRequest := ⟨.contradiction,edgeBuilt.1⟩
private def nodeRunning := (beginNode nodeRequest before).2.2
private def edgeRunning := (beginEdge edgeRequest before).2.2
private def descended := SourceCurrentAllocatedPartialGraph.descend nodeRunning .contradiction 0
/-- A deliberate active owner blocks an actual indexed walk and remains in its exact failed caller. -/
theorem node_walk_busy :
    beginNode nodeRequest before = (0,.evaluate nodeRequest,nodeRunning) ∧
    nodeCall 0 0 0 0 0 0 0 0 0 0 0 nodeRequest nodeRunning =
      .failed (.nodeMemo 0 .busy) nodeRunning ∧
    walk 1 0 0 0 0 0 0 0 0 0 0 .contradiction 0 [.empty] nodeRunning =
      .failed (.nodeMemo 0 .busy) descended.2 ∧
    descended.2.nodeResults.cells 0 = some ⟨nodeRequest,.evaluating⟩ ∧
    SourceCurrentOuterBusyOwners.RetainsOwner
      (walk 1 0 0 0 0 0 0 0 0 0 0 .contradiction 0 [.empty] nodeRunning) := by
  refine ⟨?_,?_,?_,?_,SourceCurrentOuterBusyOwners.indexed_walk ..⟩ <;> cbv
/-- A separate edge owner retains its exact caller when the literal edge demand reports busy. -/
theorem edge_busy_retained :
    beginEdge edgeRequest before = (0,.evaluate edgeRequest,edgeRunning) ∧
    edgeCall 0 0 0 0 0 0 0 0 0 0 0 edgeRequest edgeRunning =
      .failed (.edgeMemo 0 .busy) edgeRunning ∧
    edgeRunning.edgeResults.cells 0 = some ⟨edgeRequest,.evaluating⟩ ∧
    SourceCurrentOuterBusyOwners.RetainsOwner
      (edgeCall 0 0 0 0 0 0 0 0 0 0 0 edgeRequest edgeRunning) := by
  refine ⟨?_,?_,?_,SourceCurrentOuterBusyOwners.edge_call ..⟩ <;> cbv
#check @MicroCFTA.BusyOwnerKernels.node_walk_busy
#print axioms MicroCFTA.BusyOwnerKernels.node_walk_busy
#check @MicroCFTA.BusyOwnerKernels.edge_busy_retained
#print axioms MicroCFTA.BusyOwnerKernels.edge_busy_retained
end MicroCFTA.BusyOwnerKernels
