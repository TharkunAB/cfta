import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfileRoot

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 200

namespace FiniteOrdinaryOuterProfileRootKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterProfiles (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
private theorem demand_table (handle : Nat) (state : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle state).2.table = state.table := by
  cases found : state.cells handle with
  | none => simp [FlatMemoThunk.demand, found]
  | some cell => cases cell with
    | mk original status => cases status <;> simp [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus]


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)


private theorem warm_after {inventory : Inventory} {budget : Nat} {request : NodeRequest}
    {before after : Caller (bits + 2)} {result : Value Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : DNode request.value) (stored : Stored before)
    (actual : NodeCall budget request before result after) :
    ∃ handle, beginNode request after = (handle, .ready result, after) := by
  cases actual with
  | hit started =>
      have same := (stored.structural.node_ready formulas solver request _ _ result initial.sound
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent available domain started).1
      exact ⟨_, by simpa only [same] using started⟩
  | evaluate started body =>
      rename_i handle running owner middle
      obtain ⟨current, _good, _key, cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
      have frame := SourceCurrentAllocatedPartialFrames.node_body body
        (SourceCurrentAllocatedPartialFrames.Protocol.of_valid current.sound.valid)
      have published : running.nodeResults.table request.key = some handle := by
        have present : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
          change (FlatMemoThunk.demand _ _).2.table _ = _
          rw [demand_table]
          exact FlatMemoThunk.lookup_stored _ _ _
        simpa only [started] using present
      have runningCell := frame.node_running handle owner cell
      refine ⟨handle, beginNode_ready request owner _ handle result ?_ ?_⟩
      · change (FlatMemoThunk.finish handle result middle.nodeResults).table request.key = some handle
        simp only [FlatMemoThunk.finish, runningCell, FlatMemoThunk.setStatus]
        exact frame.node_keys _ _ published
      · exact finishNode_returned handle owner result middle runningCell

/-- Strong recursive construction retains the exact warm result at all ten zero worker bounds. -/
theorem finite_then_zero_bound_hit
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : NodeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : DNode request.value) (stored : Stored before)
    (active : ActiveAbove (nodeRank request) before)
    (plan : SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget (.nodeCall request before)) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : NodeCall budget request before result after,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Stored after ∧ NodeNarrow request.value result ∧
        NodeLaw formulas solver request result ∧ ActiveAbove (nodeRank request) after ∧
        SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 budget request after = .done result after := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, _available, retained, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterProfileRoot.finite bits formulas solver budget request initial inherited available
      domain stored active plan
  obtain ⟨handle, warm⟩ := warm_after formulas solver initial inherited available domain stored actual
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, retained, narrow, law,
    (SourceCurrentAllocatedPartialActiveFrames.node_call actual).activeExcept active,
    by simp only [SourceCurrentAllocatedPartialWorker.nodeCall, warm]⟩

end FiniteOrdinaryOuterProfileRootKernels
#print axioms FiniteOrdinaryOuterProfileRootKernels.finite_then_zero_bound_hit
#check @FiniteOrdinaryOuterProfileRootKernels.finite_then_zero_bound_hit
