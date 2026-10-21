import MicroCFTA.SourceCurrentOuterInitialBusy
import MicroCFTA.SourceCurrentOlderOwnerLineage

namespace MicroCFTA.SourceCurrentOlderOwnerBusy
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {bits : Nat}

theorem no_node_busy
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget handle : Nat}
    {first : Phase (bits + 2)} {inventory : Inventory} {memos : Memos}
    (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    (initialNodeIdle : ∀ chosen owner,
      (caller first).nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
    (after : Caller (bits + 2)) :
    SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first ≠
      .failed (.nodeMemo handle .busy) after

 := by
  intro failed
  obtain ⟨fuel,request,_next,_final,past,_started,_post,_frame,_fits,_known,_ready,present⟩ :=
    SourceCurrentOuterInitialBusy.busy formulas solver seed initial frame fits known inputs room failed
  have protocol : SourceCurrentOuterExecutionAncestry.NodeValid (caller first) :=
    FlatMemoThunk.Valid.keyMap _ _ _ _ initial.sound.valid.nodes (fun _ _ linked => linked.2)
  obtain ⟨ownerFuel,_requested,_before,running,earlier,activated,_key,_valid,_cell,inside⟩ :=
    past.owners protocol initialNodeIdle handle request present
  have bodyPast : Reached g s r e p h m c n budget first (.body ownerFuel request running) :=
    earlier.snoc (.node_evaluate activated)
  have rank := SourceCurrentOlderOwnerLineage.body_rank_lt formulas solver seed initial frame fits known inputs room
    normal supported causal merged positiveMemo origins bodyPast inside
  cases rank with
  | left _ _ impossible => exact Nat.lt_irrefl _ impossible
  | right _ impossible => exact Nat.lt_irrefl _ impossible

end MicroCFTA.SourceCurrentOlderOwnerBusy
