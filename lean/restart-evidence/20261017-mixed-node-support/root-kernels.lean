import MicroCFTA.SourceCurrentAllocatedPartialConditionalContinuation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MixedNodeSupportKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
open SourceCurrentAllocatedPartialConditionalActive (ActiveAbove)
open SourceCurrentAllocatedPartialActiveOrder (nodeRank)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Region" => SourceEqualityPartialPlainRegion.Region
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Two initial requests construct both actual calls and one composed receipt in mixed outer tables. -/
theorem serial
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (firstBudget secondBudget : Nat) (first second : NodeRequest)
    (initial : Context formulas solver inventory before memos)
    (firstReady : EqReady before.checked.operations.constraints first.inherited)
    (secondReady : EqReady before.checked.operations.constraints second.inherited)
    (firstAvailable : Available before.checked.native.machine.heap first.value)
    (secondAvailable : Available before.checked.native.machine.heap second.value)
    (firstRegion : Region first.value) (secondRegion : Region second.value)
    (stored : Stored before)
    (active : ActiveAbove (max (nodeRank first) (nodeRank second)) before) :
    ∃ firstResult middle secondResult after next firstMemos final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall
          f g s r e p h m c n firstBudget first before) firstResult middle ∧
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall
          f g s r e p h m c n secondBudget second middle) secondResult after ∧
      ∃ firstCall : NodeCall firstBudget first before firstResult middle,
        ∃ secondCall : NodeCall secondBudget second middle secondResult after,
          NodeCallReads formulas solver firstCall memos firstMemos ∧
          NodeCallReads formulas solver secondCall firstMemos final ∧
          Checks (nodeCallTrace firstCall) ∧ Checks (nodeCallTrace secondCall) ∧
          Post formulas solver next before after final ∧ Stored after ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver first firstResult ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver second secondResult := by
  have firstActive := SourceCurrentAllocatedPartialConditionalFrames.active_mono active (Nat.le_max_left _ _)
  have secondActive := SourceCurrentAllocatedPartialConditionalFrames.active_mono active (Nat.le_max_right _ _)
  obtain ⟨firstResult, middle, _firstNext, firstMemos, firstStable, firstCall, firstReads, firstChecks,
      _firstPost, _firstOutput, _firstStored, firstLaw⟩ :=
    SourceCurrentAllocatedPartialConditionalPlainNode.finite formulas solver firstBudget first initial firstReady
      firstAvailable firstRegion stored firstActive
  obtain ⟨secondResult, after, next, final, secondStable, secondCall, secondReads, secondChecks,
      post, _output, retained, secondLaw⟩ :=
    SourceCurrentAllocatedPartialConditionalContinuation.after_node formulas solver firstReads firstChecks initial
      firstReady firstAvailable stored secondBudget second secondReady secondAvailable secondRegion secondActive
  exact ⟨firstResult, middle, secondResult, after, next, firstMemos, final, firstStable, secondStable,
    firstCall, secondCall, firstReads, secondReads, firstChecks, secondChecks, post, retained, firstLaw, secondLaw⟩

end MicroCFTA.MixedNodeSupportKernels

#print axioms MicroCFTA.MixedNodeSupportKernels.serial
#check @MicroCFTA.MixedNodeSupportKernels.serial
