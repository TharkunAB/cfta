import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000

namespace MicroCFTA.OuterPrefixInvariantKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance
private def annotation : Guard := ⟨some [],.top⟩
private def expression : Syntax Symbol Guard :=
  .node [.mk ("parent",.top) annotation [.node [.mk ("leaf",.top) annotation []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Value Symbol Guard := ((InternedProbeProvenance.children value)[0]?).getD .empty
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def inherited : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok result => result
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def checked : SourceEqualityNativeDemand.State 4 :=
  ⟨SourceRecursiveIntersectionThunks.initial 4 ⟨heap,Cache.emptyState⟩,operations⟩
private def cold := SourceCurrentAllocatedPartialState.initial checked SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty
private def owner : NodeRequest := ⟨inherited,child⟩
private def activation := beginNode owner cold
private def running := activation.2.2
private def request : NodeRequest := ⟨inherited,value⟩
private noncomputable def execution := nodeCall 3 0 0 0 0 0 0 0 0 0 0 request running
private theorem constructed : built = .done value heap := by
  obtain ⟨result,after,done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built,value,heap,done,InternedNestedConstruction.Outcome.state]
private theorem allocation : allocated = (.ok inherited,allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) SourceEqualityGuardReadback.empty_cached allocation
private theorem initial : SourceCurrentConjunctionClassScan.Ready checked ∧ Available heap value := by
  have result := SourceCurrentConjunctionClassHistoryEntry.constructed 4 history Cache.empty_valid expression
    (fun guard member => by
      have same : guard = annotation := by simpa [expression,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards] using member
      exact same ▸ List.mem_cons_self) value heap constructed
  exact ⟨result.1,result.2.1⟩
private theorem inherited_ready : SourceEqualityConstraintAllocation.Ready operations.constraints inherited := by
  obtain ⟨result,after,done,_,ready,_,_,_⟩ := SourceEqualityConstraintAllocation.construct_complete
    annotation.equalities SourceEqualityGuardReadback.empty_cached Cache.emptyState Cache.empty_valid
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans allocation)
  cases Except.ok.inj same
  cases state
  exact ready
private theorem child_available : Available heap child :=
  initial.2.children child (by cbv; exact .head _)
private theorem cold_good : Good cold := SourceCurrentOuterPrefixInvariants.initial checked _ _
  (SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.1.good) initial.1.semantic initial.1.costs)
  (SourceCurrentMemoMergeEffects.stored_empty heap)
  (SourceCurrentMuReconstructionEffects.constructed expression value heap constructed)
private theorem activated : activation = (0,.evaluate owner,running) := by cbv
private theorem running_good : Good running :=
  (SourceCurrentOuterPrefixInvariants.activate activated cold_good ⟨inherited_ready,child_available⟩).1
private theorem actual_failure : execution = .failed (.nodeMemo 0 .busy) execution.state := by cbv

private theorem invariantProof :
    execution = .failed (.nodeMemo 0 .busy) execution.state ∧ Good execution.state ∧
      SourceEqualityConstraintMemoAllocation.Valid execution.state.checked.operations ∧
      execution.state.nodeResults.cells 1 = some ⟨request,.evaluating⟩ ∧
      ∃ fuel candidate,
        SourceCurrentOuterExecutionAncestry.Reached 0 0 0 0 0 0 0 0 0 0
          (.node 3 request running) (.node fuel candidate execution.state) ∧
        beginNode candidate execution.state = (0,.busy,execution.state) ∧ NodeReady execution.state candidate := by
  have actual : SourceCurrentOuterActiveAncestry.run 0 0 0 0 0 0 0 0 0 0 (.node 3 request running) =
      .failed (.nodeMemo 0 .busy) execution.state := by
    change execution.bind (fun _ after => .done () after) = _
    rw [actual_failure]
    rfl
  have produced := SourceCurrentOuterPrefixInvariants.busy (phase := .node 3 request running) running_good
    (show NodeReady running request from ⟨inherited_ready,initial.2⟩) actual
  exact ⟨actual_failure,produced.1,produced.1.checked.operations,by cbv,produced.2⟩

/-- An actual Parent and child-walk prefix reaches a busy child while the root owner remains active. -/
theorem constructed_busy_prefix :
    execution = .failed (.nodeMemo 0 .busy) execution.state ∧ Good execution.state ∧
      SourceEqualityConstraintMemoAllocation.Valid execution.state.checked.operations ∧
      execution.state.nodeResults.cells 1 = some ⟨request,.evaluating⟩ ∧
      ∃ fuel candidate,
        SourceCurrentOuterExecutionAncestry.Reached 0 0 0 0 0 0 0 0 0 0
          (.node 3 request running) (.node fuel candidate execution.state) ∧
        beginNode candidate execution.state = (0,.busy,execution.state) ∧ NodeReady execution.state candidate := invariantProof

end MicroCFTA.OuterPrefixInvariantKernels
