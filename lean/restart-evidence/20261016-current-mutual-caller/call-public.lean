import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_refl
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_refl
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_start
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_start
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_start
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_start
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_hit
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_hit
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_hit
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_hit
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_finish
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_finish
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_finish
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.edge_finish
#print axioms MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_binder
#check @MicroCFTA.SourceCurrentAllocatedPartialCallSteps.node_binder

namespace MicroCFTA.PartialCallStepsIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialMemoSound
open SourceCurrentAllocatedPartialInvariant
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
variable {width : Nat}
variable (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)

/-- A completed actual body installs its law at the original owner and derives the candidate law. -/
theorem node_finish_retains_owner {inventory next : Inventory} {budget : Nat} {request original : NodeRequest}
    {before running middle : Caller width} {memos final : Memos} {handle : Nat} {result : Value Symbol Guard}
    (initial : Context F S inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate original, running))
    (body : NodeBody budget original running result middle)
    (post : Post F S next running middle final)
    (resident : Available middle.checked.native.machine.heap result)
    (bodyLaw : NodeLaw F S original result) :
    Post F S next before (finishNode handle result middle) final ∧
      NodeLaw F S request result ∧
      (finishNode handle result middle).nodeResults.cells handle = some ⟨original, .returned result⟩ := by
  obtain ⟨runningContext, _, _, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start
    F S initial inherited available started
  have frame := SourceCurrentAllocatedPartialFrames.node_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have returned := finishNode_returned handle original result middle (frame.node_running handle original cell)
  obtain ⟨post, _, law⟩ := SourceCurrentAllocatedPartialCallSteps.node_finish
    F S initial inherited available started body post resident bodyLaw
  exact ⟨post, law, returned⟩

/-- The separate edge family finishes its actual running owner rather than the later candidate. -/
theorem edge_finish_retains_owner {inventory next : Inventory} {budget : Nat} {request original : EdgeRequest}
    {before running middle : Caller width} {memos final : Memos} {handle : Nat} {result : EdgeValue Symbol Guard}
    (initial : Context F S inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .evaluate original, running))
    (body : EdgeBody budget original running result middle)
    (post : Post F S next running middle final)
    (available : Resident middle.checked.native.machine.heap result)
    (bodyLaw : EdgeLaw F S original result) :
    Post F S next before (finishEdge handle result middle) final ∧
      EdgeLaw F S request result ∧
      (finishEdge handle result middle).edgeResults.cells handle = some ⟨original, .returned result⟩ := by
  obtain ⟨runningContext, _, _, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start
    F S initial inherited resident started
  have frame := SourceCurrentAllocatedPartialFrames.edge_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have returned := finishEdge_returned handle original result middle (frame.edge_running handle original cell)
  obtain ⟨post, _, law⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish
    F S initial inherited resident started body post available bodyLaw
  exact ⟨post, law, returned⟩

/-- A resident binder derives its actual body completion and law before the original owner finishes. -/
theorem binder_call {inventory : Inventory} (budget : Nat) {request : NodeRequest}
    {inherited : SourceEqualityConstraintAllocation.Value}
    {entry : Interned InternedBinderProtocol.NodeKey} {body depth ordinary : Value Symbol Guard}
    {before running : Caller width} {memos : Memos} {handle : Nat}
    (initial : Context F S inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate ⟨inherited, .mu entry body depth ordinary⟩, running)) :
    SourceEqualityMuReconstruction.rebuild entry body depth ordinary running.checked.native.machine.heap =
      .done (cleanup (.mu entry body depth ordinary)) running.checked.native.machine.heap ∧
    Post F S inventory before (finishNode handle (cleanup (.mu entry body depth ordinary)) running) memos ∧
    NodeLaw F S request (cleanup (.mu entry body depth ordinary)) ∧
    (finishNode handle (cleanup (.mu entry body depth ordinary)) running).nodeResults.cells handle =
      some ⟨⟨inherited, .mu entry body depth ordinary⟩, .returned (cleanup (.mu entry body depth ordinary))⟩ := by
  obtain ⟨runningContext, owner, _, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start
    F S initial inheritedReady available started
  have rebuilt := SourceCurrentAllocatedMuRebuild.resident_rebuild running.checked runningContext.ready
    runningContext.probes entry body depth ordinary owner.input
  have same : advance running
      (SourceCurrentAllocatedQueryMemo.advancePhysical running.checked
        ⟨running.checked.native.machine.heap, running.checked.operations⟩) running.fourth running.merge = running := by
    cases running
    rfl
  have actualBody : NodeBody budget ⟨inherited, .mu entry body depth ordinary⟩ running
      (cleanup (.mu entry body depth ordinary)) running := by
    simpa only [same] using (NodeBody.binder (inherited := inherited) rebuilt.1)
  obtain ⟨bodyPost, bodyAvailable, bodyLaw⟩ := SourceCurrentAllocatedPartialCallSteps.node_binder
    F S (inherited := inherited) runningContext owner.input rebuilt.1
  rw [same] at bodyPost
  obtain ⟨post, law, returned⟩ := node_finish_retains_owner F S initial inheritedReady available started
    actualBody bodyPost bodyAvailable bodyLaw
  exact ⟨rebuilt.1, post, law, returned⟩

#print axioms node_finish_retains_owner
#check @node_finish_retains_owner
#print axioms edge_finish_retains_owner
#check @edge_finish_retains_owner
#print axioms binder_call
#check @binder_call
end MicroCFTA.PartialCallStepsIndependent
