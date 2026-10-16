import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
namespace NumericParentCapacityKernels
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

theorem numeric_finite_then_zero_bound_hit (bits : Nat)
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.CallCapacity bits budget request before) :
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
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.finite bits formulas solver budget request initial inherited resident
      domain stored active capacity
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


theorem live_resident_field_ranges (bits : Nat)
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before)
    (live : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false) :
    ∃ loaded, SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints loaded.stored ∧
      SourceCurrentAllocatedLocalReduction.Ranges budget loaded request.inherited request.value.children
        before.checked before.fourth before.merge := by
  obtain ⟨cached, loaded, found⟩ := initial.ready.good.fields request.value.entry.key request.value resident
  have ready := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
    before.checked.operations.constraints initial.ready.good.operations.constraints cached loaded found
  have ranges := SourceCurrentAllocatedFiniteOrdinaryParentCapacity.resident_ranges bits formulas solver budget request
    initial inherited resident domain stored capacity
  exact ⟨loaded, found, ready.1, ranges live loaded found⟩

theorem captured_owner_ranges (bits : Nat)
    {inventory : Inventory} {before running : Caller (bits + 2)} {memos : Memos}
    (budget : Nat) (request owner : EdgeRequest) (handle : Nat)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.CallCapacity bits budget request before)
    (started : beginEdge request before = (handle, .evaluate owner, running)) :
    Context formulas solver inventory running memos ∧ Stored running ∧ owner.value = request.value ∧ DEdge owner.value ∧
      EqReady running.checked.operations.constraints owner.inherited ∧
      EdgeResident running.checked.native.machine.heap owner.value ∧
      running.edgeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
      SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget owner running := by
  obtain ⟨context, good, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate formulas solver
    request owner before running handle initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent
    inherited resident domain started
  have currentStored : Stored running := by simpa only [started] using stored.beginEdge request
  have checks := SourceCurrentAllocatedFiniteOrdinaryParentCapacity.call_ranges bits formulas solver budget request
    initial inherited resident domain stored capacity
  exact ⟨context, currentStored, same, ownerDomain, good.inherited, good.input, cell, checks handle owner running started⟩

#check @numeric_finite_then_zero_bound_hit
#print axioms numeric_finite_then_zero_bound_hit
#check @live_resident_field_ranges
#print axioms live_resident_field_ranges
#check @captured_owner_ranges
#print axioms captured_owner_ranges
end NumericParentCapacityKernels
