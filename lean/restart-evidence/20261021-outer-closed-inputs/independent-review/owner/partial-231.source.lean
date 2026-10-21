import MicroCFTA.SourceCurrentOuterResourceWriters
import MicroCFTA.SourceCurrentResourceParentClosed
import MicroCFTA.MergedColdReaderClosed
import MicroCFTA.InternedFreshProbeKeys

/-!
# Closed inputs through actual outer prefixes

Returned node cells preserve closure for their captured closed inputs.
The actual Parent writer supplies closure for returned edge children.
-/
namespace MicroCFTA.SourceCurrentOuterClosedInputs
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)

def NodeStored (state : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (fun request result => request.value.free = [] → result.free = []))
    state.nodeResults

def InputsClosed (phase : Phase width) : Prop :=
  match phase with
  | .node _ request _ | .body _ request _ => request.value.free = []
  | .rows _ _ values _ => MergedColdReaderClosedInputs.ClosedEdges values
  | .descendants _ _ edge _ => MergedColdReaderClosedInputs.ClosedValues edge.children
  | .children _ _ values _ | .walk _ _ _ values _ => MergedColdReaderClosedInputs.ClosedValues values

theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    NodeStored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  FlatMemoThunk.empty_valid _ _

private theorem same_nodes {before after : Caller width}
    (same : after.nodeResults = before.nodeResults) (stored : NodeStored before) : NodeStored after := by
  simpa only [NodeStored, same] using stored

private theorem begin_stored (request : NodeRequest) {before : Caller width}
    (stored : NodeStored before) : NodeStored (beginNode request before).2.2 := by
  apply FlatMemoThunk.demand_spec
  exact FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ stored rfl trivial

private theorem finish_stored (handle : Nat) (result : Node) {before : Caller width}
    (stored : NodeStored before) (closed : result.free = []) :
    NodeStored (finishNode handle result before) :=
  FlatMemoThunk.finish_spec handle result before.nodeResults _ _ stored (fun _ _ _ => closed)

variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits+2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | evaluate captured =>
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have checked := (beginEdge_components request before).1
      rw [started] at checked
      dsimp only at checked
      have bounded : Fits profile running.checked := by simpa only [checked] using fits
      have carrier : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem node_hit_closed
    {inventory : Inventory} {request : NodeRequest} {before after : Caller (bits+2)}
    {memos : Memos} {handle : Nat} {result : Node}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after))
    (stored : NodeStored before) (closed : request.value.free = []) : result.free = [] := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun observation => (observation.2.1, observation.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready result, after.nodeResults) at observed
  obtain ⟨owner,found,unchanged⟩ := FlatMemoThunk.demand_ready_original _ _ result _ observed
  have publishedStored := FlatMemoThunk.lookup_valid request.key request before.nodeResults
    (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (fun request result => request.value.free = [] → result.free = [])) stored rfl trivial
  obtain ⟨cell,present,key⟩ := publishedStored.linked request.key published.1 (FlatMemoThunk.lookup_stored _ _ _)
  have cells := Option.some.inj (present.symm.trans found)
  subst cell
  have retained : after.nodeResults.cells handle = some ⟨owner, .returned result⟩ := by
    rw [unchanged]
    have handles : published.1 = handle := congrArg Prod.fst started
    simpa only [handles] using found
  have current := (SourceCurrentAllocatedPartialCallSteps.node_hit formulas solver initial inherited available started).1.context
  have ownerGood := current.sound.nodes _ _ retained
  have checked := (beginNode_components request before).1
  rw [started] at checked
  dsimp only at checked
  have candidate : Available after.checked.native.machine.heap request.value := by simpa only [checked] using available
  have same := InternedFreshProbeKeys.resident_reference_injective after.checked.native.machine.heap
    current.ready.semantic.ready.semantic.1.normal.facts.coherent owner.value request.value
    ownerGood.input.resident candidate.resident (congrArg Prod.snd key)
  have conditional := publishedStored.checked _ _ found
  apply conditional
  simpa only [same] using closed

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem node_start_closed
    {inventory : Inventory} {request captured : NodeRequest} {before running : Caller (bits+2)}
    {memos : Memos} {handle : Nat}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate captured, running))
    (closed : request.value.free = []) : captured.value.free = [] := by
  obtain ⟨current,owner,key,_cell⟩ :=
    SourceCurrentAllocatedPartialCallSteps.node_start formulas solver initial inherited available started
  have checked := (beginNode_components request before).1
  rw [started] at checked
  dsimp only at checked
  have candidate : Available running.checked.native.machine.heap request.value := by simpa only [checked] using available
  have same := InternedFreshProbeKeys.resident_reference_injective running.checked.native.machine.heap
    current.ready.semantic.ready.semantic.1.normal.facts.coherent captured.value request.value
    owner.input.resident candidate.resident (congrArg Prod.snd key)
  simpa only [same] using closed

private theorem edge_closed
    {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller (bits+2)} {result : Edge} {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits seed.2 before.checked)
    (known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget seed.1 seed.2)
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support before.checked.native.machine.heap before.checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored Plain before.merge)
    (positive : SourceCurrentMergePositivePosition.Support before.merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver before)
    (stored : NodeStored before) (closed : ClosedValues request.value.children) :
    NodeStored after ∧ ClosedValues result.children := by
  have reserved := reservation formulas solver (request := request) initial fits known inherited resident uniform
  obtain ⟨next,final,receipt,_fits,_known⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call
    formulas solver inventory budget seed.1 request before memos initial frame seed.2 fits known inherited resident uniform actual
  have written := SourceCurrentResourceParentWriters.edge_call formulas solver inventory seed.2 memos
    actual initial frame fits inherited resident reserved origins normal supported causal merged positive
  exact ⟨same_nodes receipt.semantic.nodes stored,
    SourceCurrentResourceParentClosed.children formulas solver written.2 closed⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem modify_closed (original : Node) (oldRows newRows : List Edge)
    (before : SourceEqualityNativeDemand.State (bits+2))
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (resident : Edges before.native.machine.heap newRows)
    (closedOriginal : original.free = []) (closedRows : ClosedEdges newRows) :
    (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).1.free = [] := by
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · simpa only [SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same] using closedOriginal
  · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
      MergedColdReaderClosedInputs.makeNode_closed newRows before.native.machine.heap facts resident closedRows

variable {g s r e p h m c n budget : Nat}

private def NodeCallAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {request : NodeRequest} {before after : Caller (bits+2)} {result : Node},
    Reached g s r e p h m c n budget first (.node fuel request before) →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    NodeStored before → request.value.free = [] → NodeStored after ∧ result.free = []

private def NodeBodyAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {request : NodeRequest} {before after : Caller (bits+2)} {result : Node},
    Reached g s r e p h m c n budget first (.body fuel request before) →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    NodeStored before → request.value.free = [] → NodeStored after ∧ result.free = []

private def RowsAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {inherited : SourceEqualityConstraintAllocation.Value} {values results : List Edge} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.rows fuel inherited values before) →
    rows fuel g s r e p h m c n budget inherited values before = .done results after →
    NodeStored before → ClosedEdges values → NodeStored after ∧ ClosedEdges results

private def DescendantsAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {inherited : SourceEqualityConstraintAllocation.Value} {value result : Edge} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.descendants fuel inherited value before) →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    NodeStored before → ClosedValues value.children → NodeStored after ∧ ClosedValues result.children

private def ChildrenAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {combined : SourceEqualityConstraintAllocation.Value} {values results : List Node} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.children fuel combined values before) →
    SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done results after →
    NodeStored before → ClosedValues values → NodeStored after ∧ ClosedValues results

private def WalkAt (first : Phase (bits+2)) (fuel : Nat) : Prop :=
  ∀ {combined : SourceEqualityConstraintAllocation.Value} {index : Nat} {values results : List Node} {before after : Caller (bits+2)},
    Reached g s r e p h m c n budget first (.walk fuel combined index values before) →
    walk fuel g s r e p h m c n budget combined index values before = .done results after →
    NodeStored before → ClosedValues values → NodeStored after ∧ ClosedValues results

end MicroCFTA.SourceCurrentOuterClosedInputs
