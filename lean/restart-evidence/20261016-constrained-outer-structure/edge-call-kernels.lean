import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
namespace FiniteOrdinaryOuterEdgeCallKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove edgeRank nodeRank)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem demand_table (handle : Nat) (state : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle state).2.table = state.table := by
  cases found : state.cells handle with
  | none => simp [FlatMemoThunk.demand, found]
  | some cell =>
      cases cell with
      | mk original status =>
          cases status <;> simp [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus]

private theorem warm_after {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : EdgeValue Symbol Guard} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (actual : EdgeCall budget request before result after) :
    ∃ handle, beginEdge request after = (handle, .ready result, after) := by
  cases actual with
  | hit started =>
      have same := (stored.edge_ready formulas solver request _ _ result initial.sound
        initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident domain started).1
      exact ⟨_, by simpa only [same] using started⟩
  | evaluate started body =>
      rename_i handle running owner middle
      obtain ⟨_current, _good, _key, cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have published : running.edgeResults.table request.key = some handle := by
        have present : (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
          change (FlatMemoThunk.demand _ _).2.table _ = _
          rw [demand_table]
          exact FlatMemoThunk.lookup_stored _ _ _
        simpa only [started] using present
      cases body with
      | parent field parent =>
          rename_i loaded inherited checked fourth merge edge
          refine ⟨handle, beginEdge_ready request ⟨inherited, edge⟩ _ handle result ?_ ?_⟩
          ·
            change (FlatMemoThunk.finish handle result running.edgeResults).table request.key = some handle
            simp only [FlatMemoThunk.finish, cell, FlatMemoThunk.setStatus]
            exact published
          · exact finishEdge_returned handle _ result _ cell

/-- A genuinely constructed constrained call supports an immediate warm call at all zero bounds. -/
theorem finite_then_zero_bound_hit
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before)
    (ranges : SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.Ranges budget request before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Stored after ∧ EdgeNarrow request.value result ∧
        EdgeLaw formulas solver request result ∧
        ActiveAbove (edgeRank request) after ∧
        SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 budget request after = .done result after ∧
        (∀ child ∈ result.children, DNode child ∧ nodeRank ⟨request.inherited, child⟩ < edgeRank request) := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, _resident, retained, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.finite formulas solver budget request initial inherited resident
      domain stored active ranges
  obtain ⟨handle, warm⟩ := warm_after formulas solver initial inherited resident domain stored actual
  have activeAfter := (SourceCurrentAllocatedPartialActiveFrames.edge_call actual).activeExcept active
  refine ⟨result, after, next, final, stable, actual, reads, checks, post, retained, narrow, law, activeAfter, ?_, ?_⟩
  · simp only [SourceCurrentAllocatedPartialWorker.edgeCall, warm]
  · intro child member
    have height := SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge result child member
    have bound := narrow.2
    exact ⟨narrow.1.member child member, by
      dsimp only [nodeRank, edgeRank]
      omega⟩

/-- An actual rejected owner needs no reached machine-range premise. -/
theorem rejected_needs_no_ranges
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before)
    (rejected : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = true) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Stored after ∧ EdgeNarrow request.value result ∧
        SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 budget request after = .done result after := by
  have ranges : SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.Ranges budget request before := by
    intro handle owner running started test
    have same := (SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver request owner
      before running handle initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent
      inherited resident domain started).1
    rw [same, rejected] at test
    cases test
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, retained, narrow, _law, _active, warm, _children⟩ :=
    finite_then_zero_bound_hit formulas solver budget request initial inherited resident domain stored active ranges
  exact ⟨result, after, next, final, stable, actual, reads, checks, post, retained, narrow, warm⟩
end FiniteOrdinaryOuterEdgeCallKernels
#print axioms FiniteOrdinaryOuterEdgeCallKernels.finite_then_zero_bound_hit
#check @FiniteOrdinaryOuterEdgeCallKernels.finite_then_zero_bound_hit
#print axioms FiniteOrdinaryOuterEdgeCallKernels.rejected_needs_no_ranges
#check @FiniteOrdinaryOuterEdgeCallKernels.rejected_needs_no_ranges
