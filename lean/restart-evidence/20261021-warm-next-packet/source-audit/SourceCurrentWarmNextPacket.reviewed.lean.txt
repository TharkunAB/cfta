import MicroCFTA.SourceCurrentOuterClosedInputs
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
import MicroCFTA.SourceCurrentOuterEdgeIdle

namespace MicroCFTA.SourceCurrentWarmNextPacket
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-!
# Entry facts after a completed node call

Use the actual returned caller, inventory and memos.
Keep resources at the completed call's own scheduled seed.
This theorem supplies no future completion or capacity bound.
-/

/-- A completed call retains the facts needed for its returned value at the same caller. -/
theorem node_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget fuel : Nat}
    {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.NodeReady before request)
    (room : Room bits (SourceCurrentOuterInitialSchedule.node fuel budget seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      before.checked.native.machine.heap before.checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support before.merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver before)
    (stored : SourceCurrentOuterClosedInputs.NodeStored before)
    (closed : request.value.free = [])
    (nodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
    (edgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle before)
    (observed : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    let scheduled := SourceCurrentOuterInitialSchedule.node fuel budget seed
    ∃ next final,
      Post formulas solver next before after final ∧
      Frame formulas solver next after.checked ∧
      Fits scheduled.2 after.checked ∧
      Carrier (fun guard => guard ∈ scheduled.1) after.checked.native.machine.heap ∧
      SourceCurrentOuterPrefixInvariants.NodeReady after ⟨request.inherited, result⟩ ∧
      SourceCurrentNativeRequestPositivePositions.Support
        after.checked.native.machine.heap after.checked.native ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.checked.native.machine.heap) ∧
      SourceCurrentConstrainedCapMemoMerge.Stored
        (fun guard : Guard => SourceMemoGate.plain guard = true) after.merge ∧
      SourceCurrentMergePositivePosition.Support after.merge ∧
      SourceCurrentRequiredUnionNormal.UnionNormal after.checked.native.machine.heap ∧
      SourceCurrentResourceParentWriters.Origins formulas solver after ∧
      SourceCurrentOuterClosedInputs.NodeStored after ∧ result.free = [] ∧
      (∀ chosen owner, after.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩) ∧
      SourceCurrentOuterEdgeIdle.EdgeIdle after
 := by
  obtain ⟨next, final, actual, _reads, post, nextFrame, nextFits,
      nextKnown, available, _law⟩ :=
    SourceCurrentOuterInitialActual.node_call formulas solver fuel seed
      initial frame fits known inputs.1 inputs.2 room observed

  obtain ⟨nextSupported, nextCausal, nextMerged, nextPositive, nextNormal⟩ :=
    SourceCurrentOuterNativeStores.node_call formulas solver fuel seed
      initial frame fits known inputs.1 inputs.2 room
      normal supported causal merged positiveMemo observed

  have nextOrigins : SourceCurrentResourceParentWriters.Origins formulas solver after :=
    SourceCurrentOuterResourceWriters.node_call formulas solver fuel seed
      initial frame fits known inputs.1 inputs.2 room
      normal supported ⟨causal⟩ merged positiveMemo observed origins

  have nextClosure : SourceCurrentOuterClosedInputs.NodeStored after ∧ result.free = [] :=
    SourceCurrentOuterClosedInputs.node_call formulas solver seed
      initial frame fits known inputs room normal supported causal
      merged positiveMemo origins stored closed observed

  have inheritedAfter :
      SourceEqualityConstraintAllocation.Ready after.checked.operations.constraints
        request.inherited :=
    inputs.1.grows post.effects.grows.constraint_growth
  have nextInputs :
      SourceCurrentOuterPrefixInvariants.NodeReady after ⟨request.inherited, result⟩ :=
    ⟨inheritedAfter, available⟩

  have noNewActive :
      SourceCurrentAllocatedPartialActiveFrames.NoNewActive before after :=
    SourceCurrentAllocatedPartialActiveFrames.node_call actual
  have nextNodeIdle :
      ∀ chosen owner, after.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩ := by
    intro chosen owner present
    exact nodeIdle chosen owner (noNewActive.nodes chosen owner present)
  have nextEdgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle after := by
    intro chosen owner present
    exact edgeIdle chosen owner (noNewActive.edges chosen owner present)

  exact ⟨next, final, post, nextFrame, nextFits, nextKnown, nextInputs,
    nextSupported, nextCausal, nextMerged, nextPositive, nextNormal,
    nextOrigins, nextClosure.1, nextClosure.2, nextNodeIdle, nextEdgeIdle⟩

end MicroCFTA.SourceCurrentWarmNextPacket
