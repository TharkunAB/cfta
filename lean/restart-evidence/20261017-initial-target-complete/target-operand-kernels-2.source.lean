import MicroCFTA.SourceCurrentConstrainedCapTargetOperand
import MicroCFTA.EndpointMemoGateSource
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.TargetOperandIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedTargetGraph (Operand)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "Forecast" => SourceCurrentConstrainedCapTargetForecast.operand
local notation "Fuel" => SourceCurrentConstrainedCapTargetForecast.operandFuel
local notation "worker" => SourceCurrentAllocatedTargetWorker.operand
variable {width : Nat}

private theorem selected_domain (value : Value Symbol Guard) (closed : value.free = []) :
    Domain [0] [value, .reference .depth] := by
  intro child found
  have same : value = child := Option.some.inj found
  subst child
  exact closed
private theorem selected_available (state : Checked width) (value : Value Symbol Guard)
    (available : Available state.native.machine.heap value) :
    Values state.native.machine.heap [value, .reference .depth] := by
  intro original member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · exact List.mem_singleton.mp member ▸ InternedNestedProvenance.depth_available _
private theorem selected_caps (depth : Nat) (value : Value Symbol Guard) (bounded : Cap depth value) :
    ∀ original ∈ [value, Value.reference .depth], Cap depth original := by
  intro original member
  rcases List.mem_cons.mp member with rfl | member
  · exact bounded
  · have same := List.mem_singleton.mp member
    subst original
    exact .plain depth (.reference _)
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : Memo) := by
  intro ambient key entry absent
  cases absent

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A produced Operand result enters a second initial-profile call beside an unrelated open root. -/
theorem result_fed (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (profile : Profile) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (value : Value Symbol Guard)
    (available : Available before.native.machine.heap value) (closed : value.free = []) (bounded : Cap depth value)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ¬MergedColdReaderClosedInputs.ClosedValues [value, Value.reference .depth] ∧
    ∃ first middle firstMemo current result after saved final,
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] [value, .reference .depth]
        before SourceCurrentMemoMergeGraph.empty first middle firstMemo memos current ∧
      worker (Fuel [0] 2 profile) (Fuel [0] 2 profile) (Fuel [0] 2 profile) (Fuel [0] 2 profile)
        [0] [value, .reference .depth] before SourceCurrentMemoMergeGraph.empty = .done first middle firstMemo ∧
      Fits (Forecast [0] 2 profile) middle ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] [first, .reference .depth]
        middle firstMemo result after saved current final ∧
      worker (Fuel [0] 2 (Forecast [0] 2 profile)) (Fuel [0] 2 (Forecast [0] 2 profile))
        (Fuel [0] 2 (Forecast [0] 2 profile)) (Fuel [0] 2 (Forecast [0] 2 profile))
        [0] [first, .reference .depth] middle firstMemo = .done result after saved ∧
      Frame formulas solver inventory after ∧ Fits (Forecast [0] 2 (Forecast [0] 2 profile)) after ∧
      Cap depth result ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final := by
  obtain ⟨first, middle, firstMemo, current, _firstGraph, firstReceipt, firstFrame, firstFits, firstDone, firstStored, firstCap⟩ :=
    SourceCurrentConstrainedCapTargetOperand.mixed_complete depth formulas solver inventory [0]
      [value, .reference .depth] before SourceCurrentMemoMergeGraph.empty profile frame fits
      (selected_available before value available) (selected_domain value closed)
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver) memos valid
      (SourceCurrentConstrainedCapMemoMerge.stored_empty Plain) (selected_caps depth value bounded)
  have firstBounded : Cap depth first := firstCap
  obtain ⟨result, after, saved, final, _lastGraph, lastReceipt, lastFrame, lastFits, lastDone, _lastStored, lastCap⟩ :=
    SourceCurrentConstrainedCapTargetOperand.mixed_complete depth formulas solver inventory [0]
      [first, .reference .depth] middle firstMemo (Forecast [0] 2 profile) firstFrame firstFits
      (selected_available middle first firstReceipt.available) (selected_domain first firstReceipt.closed)
      firstReceipt.stored firstReceipt.covered current firstReceipt.globals firstStored
      (selected_caps depth first firstBounded)
  refine ⟨?_, first, middle, firstMemo, current, result, after, saved, final,
    firstReceipt, firstDone, firstFits, lastReceipt, lastDone, lastFrame, lastFits, lastCap,
    lastReceipt.nodes.trans firstReceipt.nodes, lastReceipt.edges.trans firstReceipt.edges,
    lastReceipt.domains.trans firstReceipt.domains, lastReceipt.globals⟩
  intro impossible
  have bad := impossible (.reference .depth) (by simp)
  cases bad

/-- Signed absent positions construct their own full worker return at all larger independent fuels. -/
theorem signed_missing (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (profile : Profile) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) :
    ∃ result after saved final,
      Operand [-1] [Value.reference .depth] before SourceCurrentMemoMergeGraph.empty result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [-1] [Value.reference .depth]
        before SourceCurrentMemoMergeGraph.empty result after saved EndpointMemoGateTrace.empty final ∧
      Frame formulas solver inventory after ∧ Fits (Forecast [-1] 1 profile) after ∧
      ∀ projectionExtra readExtra mergeExtra selectionExtra,
        worker (Fuel [-1] 1 profile + projectionExtra) (Fuel [-1] 1 profile + readExtra)
          (Fuel [-1] 1 profile + mergeExtra) (Fuel [-1] 1 profile + selectionExtra)
          [-1] [Value.reference .depth] before SourceCurrentMemoMergeGraph.empty = .done result after saved := by
  have available : Values before.native.machine.heap [Value.reference .depth] := by
    intro value member
    exact List.mem_singleton.mp member ▸ InternedNestedProvenance.depth_available _
  have selected : Domain [-1] ([Value.reference .depth] : List (Value Symbol Guard)) := by
    intro value found
    cases found
  obtain ⟨result, after, saved, final, actual, receipt, returned, numeric, done⟩ :=
    SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory [-1] [Value.reference .depth]
      before SourceCurrentMemoMergeGraph.empty profile frame fits available selected
      (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid _)
  exact ⟨result, after, saved, final, actual, receipt, returned, numeric,
    fun projectionExtra readExtra mergeExtra selectionExtra =>
      SourceCurrentAllocatedTargetWorkerCompletion.operand_done_stable done
        (Nat.le_add_right _ _) (Nat.le_add_right _ _) (Nat.le_add_right _ _) (Nat.le_add_right _ _)⟩
end MicroCFTA.TargetOperandIntegration

#print axioms MicroCFTA.TargetOperandIntegration.result_fed
#check @MicroCFTA.TargetOperandIntegration.result_fed
#print axioms MicroCFTA.TargetOperandIntegration.signed_missing
#check @MicroCFTA.TargetOperandIntegration.signed_missing
