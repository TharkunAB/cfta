import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.ActualOuterWorkChecks
private theorem demand_table {Key Request Result : Type} (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase, FlatMemoThunk.setStatus]

private theorem finish_table {Key Request Result : Type} (handle : Nat) (result : Result) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.finish handle result memo).table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk request status => cases status <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]


open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers (nodeRows nodeGuards)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height edgesHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- The body can allocate and make descendant calls. Its frame retains the
-- original published key while finish installs the derived universal law.
theorem evaluated_node_counts_then_zero_warm
    (inventory : Inventory) {request owner : NodeRequest} {before running middle : Caller width}
    {result : Node} {handle : Nat} {memos final : Memos}
    {body : NodeBody budget owner running result middle}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (domain : DNode request.value) (stored : Stored before)
    (started : beginNode request before = (handle, .evaluate owner, running))
    (bodyReads : NodeBodyReads formulas solver body memos final)
    (rows arity bound : Nat) (limits : Limits) (profile : NodeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : height request.value ≤ bound) :
    let after := finishNode handle result middle
    ∃ actual : NodeCall budget request before result after,
      NodeCallReads formulas solver actual memos final ∧ Stored after ∧
      after.nodeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      NodeCertificate owner result ∧ NodeCertificate request result ∧
      beginNode request after = (handle, .ready result, after) ∧
      SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
        (SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.nodeNodes rows arity limits bound)
        (SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.nodeEdges rows arity limits bound) ∧
      SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.WorkBounds after.checked.native.machine.heap after.checked.native.machine.heap 0 0 := by
  let actual : NodeCall budget request before result (finishNode handle result middle) := .evaluate started body
  have reads : NodeCallReads formulas solver actual memos final := .evaluate (started := started) bodyReads
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_call formulas solver reads inventory
    initial inherited available domain stored
  obtain ⟨runningContext, _ownerFacts, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
    initial inherited available started
  have frame := SourceCurrentAllocatedPartialFrames.node_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have returned := finishNode_returned handle owner result middle (frame.node_running handle owner cell)
  have published : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  rw [started] at published
  have finalPublished : (finishNode handle result middle).nodeResults.table request.key = some handle := by
    change (FlatMemoThunk.finish handle result middle.nodeResults).table request.key = some handle
    rw [finish_table]
    exact frame.node_keys request.key handle published
  have counts := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.node_call formulas solver reads inventory
    initial inherited available domain stored rows arity bound limits profile guards heightBound
  exact ⟨actual, reads, produced.1, returned, produced.1.returned.nodes handle owner result returned,
    produced.2.2, beginNode_ready request owner _ handle result finalPublished returned,
    counts, SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.WorkBounds.refl _⟩


-- Count bounds and the same actual Post imply final constructor supplies.
-- No final counter difference is used as a request-count premise.
theorem actual_rows_supplies
    (inventory : Inventory) {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : InternedNestedProvenance.Edges before.checked.native.machine.heap values)
    (domain : DRows values) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : RowsShape rows arity values)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits values)
    (heightBound : edgesHeight values ≤ bound) :
    ∃ next requests,
      SourceCurrentAllocatedPartialInvariant.Post formulas solver next before after final ∧ Stored after ∧
      SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace
        before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.nodeRequests requests ≤
        values.length * SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.rowNodes rows arity limits bound ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.edgeRequests requests ≤
        values.length * SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.rowEdges rows arity limits bound ∧
      results.length = values.length ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next +
        values.length * SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.rowNodes rows arity limits bound ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next +
        values.length * SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.rowEdges rows arity limits bound := by
  obtain ⟨requests, trace, nodes, edges⟩ := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.rows formulas solver reads inventory
    initial inheritedReady available domain stored rows arity bound limits profile guards heightBound
  have quantitative := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.rows formulas solver reads inventory
    initial inheritedReady available domain stored
  have checked := SourceCurrentAllocatedFiniteOrdinaryOuterVerification.rows formulas solver reads inventory
    initial inheritedReady available domain stored.structural
  obtain ⟨next, post, _resident, _retained, _narrow⟩ := checked.2
  have supplies := trace.next_le
  exact ⟨next, requests, post, quantitative.1, trace, nodes, edges, actual.length,
    Nat.le_trans supplies.1 (Nat.add_le_add_left nodes _), Nat.le_trans supplies.2 (Nat.add_le_add_left edges _)⟩

#print axioms evaluated_node_counts_then_zero_warm
#check @evaluated_node_counts_then_zero_warm
#print axioms actual_rows_supplies
#check @actual_rows_supplies
end MicroCFTA.ActualOuterWorkChecks
