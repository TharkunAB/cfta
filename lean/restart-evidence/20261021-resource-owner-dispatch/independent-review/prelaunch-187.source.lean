import MicroCFTA.SourceCurrentResourceOwnerProgress
import MicroCFTA.SourceCurrentOuterResourceWriters
import MicroCFTA.SourceCurrentOuterUntouchedProgress
import MicroCFTA.SourceCurrentOuterInitialActual
import MicroCFTA.SourceCurrentOuterExecutionGrowth

namespace MicroCFTA.SourceCurrentResourceOwnerDispatch
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
variable {bits : Nat}

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits + 2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
      before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
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
      have carrier : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
          running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem key_ne_top
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget fuel slot handle identity : Nat}
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
    {ownerEntry ownerDepth ownerFree} {ownerRows : List Edge}
    {original parented : Edge} {rest : List Edge}
    {before afterParent start : Caller (bits + 2)} {earlier : List Node}
    {combined : EqValue} {value : Node}
    (past : Reached g s r e p h m c n budget first
      (.rows (fuel + slot + 2) (.live identity []) (original :: rest) before))
    (active : before.nodeResults.cells handle = some
      ⟨⟨.live identity [], .node ownerEntry ownerRows ownerDepth ownerFree⟩, .evaluating⟩)
    (member : original ∈ ownerRows)
    (parent : edgeCall (fuel + slot + 1) g s r e p h m c n budget
      ⟨.live identity [], original⟩ before = .done parented afterParent)
    (combinedAt : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
      (.live identity []) afterParent.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined 0
      (parented.children.take slot) (prefixState afterParent parented (.live identity [])) =
        .done earlier start)
    (selected : parented.children[slot]? = some value) :
    Reached g s r e p h m c n budget first
      (.node fuel ⟨(descend start combined slot).1, value⟩ (descend start combined slot).2) ∧
      (NodeRequest.mk (descend start combined slot).1 value).key ≠
        (NodeRequest.mk (.live identity []) (.node ownerEntry ownerRows ownerDepth ownerFree)).key
 := by
  obtain ⟨rowInventory,rowMemos,rowSeed,_rowTrace,rowPost,rowFrame,rowFits,rowKnown,
      rowInputs,_rowBelow,_rowAlphabet,rowRoom,_rowBounds,_rowCarrier,_rowNeed,
      rowSupport,⟨rowCausal⟩,rowMerged,rowPositive,rowNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed past initial frame fits known inputs room
      normal supported causal merged positiveMemo
  have rowOrigins := SourceCurrentOuterResourceWriters.reached formulas solver seed past
    initial frame fits known inputs room normal supported causal merged positiveMemo origins
  have headRoom := rowRoom
  change Room bits (SourceCurrentOuterInitialSchedule.rows ((fuel + slot + 1) + 1) budget rowSeed).2 at headRoom
  rw [SourceCurrentOuterInitialSchedule.rows] at headRoom
  let parentSeed := SourceCurrentOuterInitialSchedule.parent budget rowSeed
  have parentRoom : Room bits parentSeed.2 := headRoom.mono
    ((SourceCurrentOuterInitialSchedule.descendants_ge (fuel + slot + 1) budget parentSeed).1.trans
      (SourceCurrentOuterInitialSchedule.rows_ge (fuel + slot + 1) budget
        (SourceCurrentOuterInitialSchedule.descendants (fuel + slot + 1) budget parentSeed)).1)
  have uniform := SourceCurrentOuterInitialSchedule.parent_reserved bits budget rowSeed parentRoom
  have reserved := reservation formulas solver (request := ⟨.live identity [],original⟩)
    rowPost.context rowFits rowKnown rowInputs.1 (rowInputs.2 _ List.mem_cons_self) uniform
  have written := (SourceCurrentResourceParentWriters.edge_call formulas solver rowInventory rowSeed.2 rowMemos
    parent rowPost.context rowFrame rowFits rowInputs.1 (rowInputs.2 _ List.mem_cons_self) reserved
    rowOrigins rowNormal rowSupport rowCausal rowMerged rowPositive).2
  have rowStep : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) (.live identity []) (original :: rest) before)
      (.descendants (fuel + slot + 1) (.live identity []) parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent)
  have descReached := past.trans rowStep
  have walkLocal := (rowStep.snoc (SourceCurrentOuterExecutionAncestry.Step.descendants_children combinedAt)).snoc
    (SourceCurrentOuterExecutionAncestry.Step.children_walk live)
  have walkReached := past.trans walkLocal
  have selectedPrefix := SourceCurrentOuterUntouchedProgress.walk_prefix earlierCalls selected
  have dispatchLocal : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) (.live identity []) (original :: rest) before)
      (.node fuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) := by
    simpa only [Nat.zero_add] using walkLocal.trans selectedPrefix
  have dispatchReached := past.trans dispatchLocal
  obtain ⟨descInventory,descMemos,_descSeed,_descTrace,descPost,_descFrame,_descFits,_descKnown,
      descInputs,_descBelow,_descAlphabet,_descRoom,_descBounds,_descCarrier,_descNeed,
      _descSupport,_descHistory,_descMerged,_descPositive,_descNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed descReached initial frame fits known inputs room
      normal supported causal merged positiveMemo
  have field := descPost.context.ready.good.fields parented.entry.key parented descInputs.2
  obtain ⟨walkInventory,walkMemos,walkSeed,_walkTrace,walkPost,walkFrame,walkFits,walkKnown,
      walkInputs,_walkBelow,_walkAlphabet,walkRoom,_walkBounds,_walkCarrier,_walkNeed,
      _walkSupport,_walkHistory,_walkMerged,_walkPositive,_walkNormal⟩ :=
    SourceCurrentOuterPrefixNativeStores.reached formulas solver seed walkReached initial frame fits known inputs room
      normal supported causal merged positiveMemo
  obtain ⟨startInventory,startMemos,_walkGraph,_walkReads,startPost,_startFrame,_startFits,
      _startKnown,_startValues,_startLaw⟩ :=
    SourceCurrentOuterInitialActual.walk formulas solver (fuel + slot + 1)
      (combined := combined) (index := 0) (values := parented.children.take slot)
      (before := prefixState afterParent parented (.live identity [])) (after := start)
      walkSeed walkPost.context walkFrame walkFits walkKnown walkInputs.1
      (fun child member => walkInputs.2 child (List.mem_of_mem_take member)) walkRoom earlierCalls
  have protocol : SourceCurrentOuterExecutionAncestry.NodeValid before :=
    FlatMemoThunk.Valid.keyMap _ _ _ _ rowPost.context.sound.valid.nodes (fun _ _ linked => linked.2)
  have activeAtDispatch := dispatchLocal.running protocol handle
    ⟨.live identity [],.node ownerEntry ownerRows ownerDepth ownerFree⟩ active
  have activeAtStart : start.nodeResults.cells handle = some
      ⟨⟨.live identity [],.node ownerEntry ownerRows ownerDepth ownerFree⟩,.evaluating⟩ := activeAtDispatch
  refine ⟨dispatchReached,?_⟩
  intro collision
  have sameReference : value.referenceOf = (.node ownerEntry ownerRows ownerDepth ownerFree).referenceOf :=
    congrArg Prod.snd collision
  have ownerGood := startPost.context.sound.nodes handle _ activeAtStart
  have childAvailable := startPost.effects.keeps.available value
    (walkInputs.2 value (List.mem_of_getElem? selected))
  have sameValue := SourceEqualityPartialKeyTransport.available_reference_eq _
    startPost.context.ready.semantic.ready.semantic.1.normal.facts.coherent value
    (.node ownerEntry ownerRows ownerDepth ownerFree) childAvailable ownerGood.input sameReference
  have foundOwner : parented.children[slot]? = some (.node ownerEntry ownerRows ownerDepth ownerFree) := by
    simpa only [sameValue] using selected
  have laterGrowth : SourceEqualityConstraintMemoAllocation.Grows
      (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint
        (.live identity []) afterParent.checked.operations).2 start.checked.operations := startPost.effects.grows
  have excluded := SourceCurrentResourceOwnerProgress.key_ne_top formulas solver written member foundOwner
    afterParent.checked.operations descPost.context.ready.good.operations descInputs.1 field combined combinedAt live
    start.checked.operations startPost.context.ready.good.operations laterGrowth identity descInputs.1
  have sameKey : (NodeRequest.mk (descend start combined slot).1
      (.node ownerEntry ownerRows ownerDepth ownerFree)).key =
        (NodeRequest.mk (.live identity []) (.node ownerEntry ownerRows ownerDepth ownerFree)).key := by
    simpa only [sameValue] using collision
  exact excluded.2.2.2 sameKey

end MicroCFTA.SourceCurrentResourceOwnerDispatch
