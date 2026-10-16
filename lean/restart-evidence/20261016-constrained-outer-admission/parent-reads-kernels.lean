import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterParentReads

namespace MicroCFTA.OuterParentReadIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialInvariant
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- The captured evaluating owner receives strict reads before its same protected finish. -/
theorem evaluated_owner (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget handle : Nat} {request owner : EdgeRequest}
    {before running middle : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (body : EdgeBody budget owner running result middle) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget owner running) :
    ∃ final next,
      EdgeBodyReads formulas solver body memos final ∧
      EdgeCallReads formulas solver (.evaluate started body) memos final ∧
      Post formulas solver next before (finishEdge handle result middle) final ∧
      Stored (finishEdge handle result middle) ∧
      EdgeResident (finishEdge handle result middle).checked.native.machine.heap result ∧
      EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨current, ready, key, cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
  obtain ⟨same, ownerDomain, ownerKey⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate
    formulas solver request owner before running handle initial.sound
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
  have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
  obtain ⟨final, reads, checks, next, post, available, middleStored, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.verified bits formulas solver body inventory
      current ready.inherited ready.input ownerDomain runningStored capacity
  obtain ⟨finished, resultResident, candidateLaw⟩ := SourceCurrentAllocatedPartialCallSteps.edge_finish
    formulas solver initial inherited resident started body post available law
  have evaluatingCell := (SourceCurrentAllocatedPartialFrames.edge_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid current.sound.valid)).edge_running handle owner cell
  have finishedStored := middleStored.finishEdge result evaluatingCell (fun _ => narrow)
  exact ⟨final, next, reads, .evaluate (started := started) reads, finished, finishedStored, resultResident,
    by simpa only [same] using narrow, candidateLaw⟩

/-- Two supplied parent bodies compute their own strict schedules at the same warm middle state. -/
theorem serial_parents (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {first second : EdgeRequest} {before middle after : Caller (bits + 2)}
    {firstResult secondResult : EdgeValue Symbol Guard}
    (firstBody : EdgeBody budget first before firstResult middle)
    (secondBody : EdgeBody budget second middle secondResult after)
    (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints first.inherited)
    (resident : EdgeResident before.checked.native.machine.heap first.value)
    (domain : DEdge first.value) (stored : Stored before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget first before)
    (secondInherited : EqReady middle.checked.operations.constraints second.inherited)
    (secondResident : EdgeResident middle.checked.native.machine.heap second.value)
    (secondDomain : DEdge second.value)
    (secondCapacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget second middle) :
    ∃ current final next,
      EdgeBodyReads formulas solver firstBody memos current ∧
      EdgeBodyReads formulas solver secondBody current final ∧
      Post formulas solver next before after final ∧ Stored after := by
  obtain ⟨current, reads, checks, next, post, available, currentStored, narrow, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.verified bits formulas solver firstBody inventory
      initial inherited resident domain stored capacity
  obtain ⟨final, nextReads, nextChecks, finalInventory, nextPost, nextAvailable, finalStored, nextNarrow, nextLaw⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.verified bits formulas solver secondBody next
      post.context secondInherited secondResident secondDomain currentStored secondCapacity
  exact ⟨current, final, finalInventory, reads, nextReads, post.trans nextPost, finalStored⟩

end MicroCFTA.OuterParentReadIntegration

#print axioms MicroCFTA.OuterParentReadIntegration.evaluated_owner
#check @MicroCFTA.OuterParentReadIntegration.evaluated_owner
#print axioms MicroCFTA.OuterParentReadIntegration.serial_parents
#check @MicroCFTA.OuterParentReadIntegration.serial_parents
