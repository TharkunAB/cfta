import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.OuterEdgeShapesIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)


theorem same_body_post_and_certificate {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before) :
    ∃ next, SourceCurrentAllocatedPartialInvariant.Post formulas solver next before after final ∧
      EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧ EdgeNarrow request.value result ∧
      EdgeCertificate request result ∧ SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body formulas solver reads inventory
    initial inherited resident domain stored
  have verified := SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory
    initial inherited resident domain stored.structural
  obtain ⟨next, post, output, _retained, _narrowed, law⟩ := verified.2
  exact ⟨next, post, output, produced.1, produced.2.1, produced.2.2, law⟩

/-- A successful body derives its owner law before finish, then a literal repeat is an exact-state warm hit. -/
theorem evaluated_owner_then_warm
    (inventory : Inventory) {request owner : EdgeRequest} {before running middle : Caller width}
    {result : Edge} {handle : Nat} {memos final : Memos}
    {body : EdgeBody budget owner running result middle}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (bodyReads : EdgeBodyReads formulas solver body memos final) :
    let after := finishEdge handle result middle
    ∃ actual : EdgeCall budget request before result after,
      EdgeCallReads formulas solver actual memos final ∧ Stored after ∧
      after.edgeResults.cells handle = some ⟨owner, .returned result⟩ ∧
      EdgeCertificate owner result ∧ EdgeCertificate request result ∧
      beginEdge request after = (handle, .ready result, after) := by
  let actual : EdgeCall budget request before result (finishEdge handle result middle) := .evaluate started body
  have reads : EdgeCallReads formulas solver actual memos final := .evaluate bodyReads
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_call formulas solver reads inventory
    initial inherited resident domain stored
  obtain ⟨runningContext, _ownerFacts, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver
    initial inherited resident started
  have frame := SourceCurrentAllocatedPartialFrames.edge_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have returned := finishEdge_returned handle owner result middle (frame.edge_running handle owner cell)
  have tables : middle.edgeResults = running.edgeResults := by cases body; rfl
  have published : (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  rw [started] at published
  have finalPublished : (finishEdge handle result middle).edgeResults.table request.key = some handle := by
    change (FlatMemoThunk.finish handle result middle.edgeResults).table request.key = some handle
    rw [FlatMemoThunk.finish_table, tables]
    exact published
  exact ⟨actual, reads, produced.1, returned, produced.1.returned.edges handle owner result returned,
    produced.2.2, beginEdge_ready request owner _ handle result finalPublished returned⟩

end MicroCFTA.OuterEdgeShapesIntegration

#print axioms MicroCFTA.OuterEdgeShapesIntegration.same_body_post_and_certificate
#check @MicroCFTA.OuterEdgeShapesIntegration.same_body_post_and_certificate
#print axioms MicroCFTA.OuterEdgeShapesIntegration.evaluated_owner_then_warm
#check @MicroCFTA.OuterEdgeShapesIntegration.evaluated_owner_then_warm
