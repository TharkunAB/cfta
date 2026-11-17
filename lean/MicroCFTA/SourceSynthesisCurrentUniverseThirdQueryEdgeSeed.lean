import MicroCFTA.SourceSynthesisCurrentUniverseThirdQueryNodeSeed
import MicroCFTA.SourceCurrentNativeWarmEdgeFinish

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Third-history edge seeds through actual retained child cells]
The source theorem derives the node seed at the exact middle snapshot.
Each edge origin retains its own producing query and original row order.
The checked edge body gives every actual completed child cell.
The actual suffix and any separate middle query retain that SAME cell.
No independent query controls are concatenated into one native trace.
No node law or desired child Profile is a public source premise.
-/

private theorem third_edge_closed_codec (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem third_edge_key_of_codecs {width : Nat} (request : NodeRequest Symbol Guard)
    (left : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (right : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  obtain ⟨first, firstInput⟩ := left
  obtain ⟨second, secondInput⟩ := right
  exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    first second firstInput secondInput⟩

private theorem third_edge_qualified_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (request : NodeRequest Symbol Guard)
    (qualified : Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases qualified with closed | mixed
  · exact third_edge_key_of_codecs (width := width) request (third_edge_closed_codec _ closed.1.1) (third_edge_closed_codec _ closed.2.1.1)
  · obtain ⟨pattern, patternId, openAlias, operand, _authentic, alias, operandProfile,
      _height, _strict, ordered⟩ := mixed
    have aliasCodec : ∃ input, IntersectionFlatMemoKey.input openAlias.referenceOf = some input := by
      rcases alias with rfl | rfl
      · exact bodyCodec
      · exact ⟨.ref entry.identity, rfl⟩
    have operandCodec := third_edge_closed_codec _ operandProfile.1
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact third_edge_key_of_codecs (width := width) request (by rw [left]; exact aliasCodec) (by rw [right]; exact operandCodec)
    · exact third_edge_key_of_codecs (width := width) request (by rw [left]; exact operandCodec) (by rw [right]; exact aliasCodec)

private theorem producer_edge_profiles_at_target_nodes
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (producerRoot : NodeRequest Symbol Guard) (producerStart : Checked width)
    (initialPhysical : Physical producerStart.native)
    (sourceGrowth : Grows sourceHeap producerStart.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid producerStart.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard)
    (rest : Control Node) (producerEnd beforeFinish : Checked width)
    (parentNext : Code Symbol Guard Node)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node producerRoot .pure)) producerStart rest producerEnd)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node producerRoot .pure)) producerStart
      (.code (.finishEdge handle row parentNext)) beforeFinish)
    (owner : beforeFinish.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node producerRoot .pure)) producerStart)
    (fields : FieldsThrough fuel (.code (.node producerRoot .pure)) producerStart)
    (targetRoot : NodeRequest Symbol Guard) (targetStart : Checked width) (targetCount : Nat)
    (nodeSeed : Returned (NodeResult (width := width) targetRoot targetStart targetCount
      entry body depth ordinary) targetStart.native.nodes)
    (retained : SourceEqualityNativeDemandMemo.Retained producerEnd.native targetStart.native) :
    EdgeResult (width := width) targetRoot targetStart targetCount entry body depth ordinary request row := by
  intro originalQualified
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, _queryBound, queryPrefix, _actualDispatch, isolatedDispatch,
      queryPhysical, _queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin.actual_edge_query_dispatch_from_warm_query_finish
      producerRoot producerStart initialPhysical fuel finishUsed handle request row parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node producerRoot .pure)) producerStart
      ((Control.code (.edge request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node producerRoot .pure)) (.code (.edge request .pure)) queryResume
      producerStart queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  have trueReturned :
      Returned (fun (_ : NodeRequest Symbol Guard) (_ : Node) => True) producerEnd.native.nodes ∧
      Returned (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
        producerEnd.native.edges :=
    ⟨fun _ _ _ _ => True.intro, fun _ _ _ _ => True.intro⟩
  have observed := SourceCurrentAllocatedNativeCheckedEdgeBodyProfile.edge_body_children_profile_of_fuel_induction
    sourceHeap entry.identity request queryBefore beforeBody beforeFinish (fuel - queryUsed) bodyCount row
    (fun result => .finishEdge handle result (.pure result))
    queryPhysical queryGrowth queryOperations queryInputs queryFields isolatedDispatch (by omega) rawBody (by
      intro pair member used childFuel childCount _positive _childSmaller _childFuelBound
        _childCountBound childSpan next first last value origin _childPhysical _childGrowth
        _childOperations _childInputs _childFields _leftAvailable _rightAvailable childActual
      let child : NodeRequest Symbol Guard := ⟨request.domain, pair.1, pair.2⟩
      have qualified : Qualified (width := width) targetRoot targetStart targetCount
          entry body depth ordinary child := originalQualified pair member
      obtain ⟨childKey, keyed⟩ := third_edge_qualified_key targetRoot targetStart targetCount
        entry body depth ordinary bodyCodec child qualified
      let lifted : Node → Code Symbol Guard Node := fun result => (next result).bind queryResume
      have appended := origin.bind _ _ _ _ _ queryResume
      change Steps used (.code (.edge request queryResume)) queryBefore
        (.code (((requestNode request.domain pair.1 pair.2).bind next).bind queryResume)) first at appended
      have tail : Steps used (.code (.edge request queryResume)) queryBefore
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Code.bind_assoc, lifted] using appended
      have outer : Steps (queryUsed + used) (.code (.node producerRoot .pure)) producerStart
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first :=
        queryPrefix.steps.trans _ _ _ _ _ _ _ _ tail
      have receipt :=
        SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
          (fun (_ : NodeRequest Symbol Guard) (_ : Node) => True)
          (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
          producerRoot producerStart initialPhysical fuel wholeCount (queryUsed + used) childCount
          rest producerEnd wholeBound wholeActual trueReturned child childKey keyed
          lifted first last value (by omega) outer childActual
      obtain ⟨childHandle, _childAtReturn, childAtProducer, _actualChildSuffix, _childRetention⟩ := receipt.2
      have childAtTarget := retained.nodes childHandle child value childAtProducer
      have currentLaw := nodeSeed childHandle child value childAtTarget
      rcases qualified with closed | mixed
      · exact currentLaw.1 closed
      · exact currentLaw.2 mixed)
  exact observed.1

theorem original_universe_two_prefix_edge_seed_for_third_actual_history
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (oldFuel oldCount : Nat) (oldControl : Control (Value Symbol Guard))
    (oldSnapshot : Checked width) (oldBound : oldCount ≤ oldFuel)
    (oldInputs : InputsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldFields : FieldsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldActual : Trace oldCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
    (middleRoot : NodeRequest Symbol Guard) (middleFuel : Nat)
    (middleRootDomain : middleRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (middleLeftAvailable : Available oldSnapshot.native.machine.heap middleRoot.left)
    (middleRightAvailable : Available oldSnapshot.native.machine.heap middleRoot.right)
    (middleLeftClosed : middleRoot.left.free = []) (middleRightClosed : middleRoot.right.free = [])
    (middleInputs : InputsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleFields : FieldsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleCount : Nat) (middleControl : Control (Value Symbol Guard))
    (middleSnapshot : Checked width) (middleBound : middleCount ≤ middleFuel)
    (middleActual : Trace middleCount (.code (.node middleRoot .pure))
      oldSnapshot middleControl middleSnapshot)
    (nextRoot : NodeRequest Symbol Guard) (nextFuel nextCount : Nat)
    (nextControl : Control (Value Symbol Guard)) (reader : Checked width)
    (nextRootDomain : nextRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (nextRootAvailable : Available middleSnapshot.native.machine.heap nextRoot.left ∧
      Available middleSnapshot.native.machine.heap nextRoot.right)
    (nextRootClosed : nextRoot.left.free = [] ∧ nextRoot.right.free = [])
    (nextBound : nextCount ≤ nextFuel)
    (nextInputs : InputsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextFields : FieldsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextActual : Trace nextCount (.code (.node nextRoot .pure)) middleSnapshot
      nextControl reader) :
    Returned (SourceCurrentNativeWarmCMDefinitions.EdgeResult (width := width)
      nextRoot middleSnapshot nextCount entry body depth ordinary) middleSnapshot.native.edges := by
  have nodeSeed := original_universe_two_prefix_node_seed_for_third_actual_history (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
    middleInputs middleFields middleCount middleControl middleSnapshot middleBound middleActual
    nextRoot nextFuel nextCount nextControl reader nextRootDomain nextRootAvailable nextRootClosed
    nextBound nextInputs nextFields nextActual
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have middleRetained := SourceCurrentNativeWriterReadyRetention.trace_retained middleActual
    oldOperations.2.1.shape
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  intro handle request row currentCell
  rcases SourceCurrentAllocatedNativeEdgeReturnOrigin.returned_edge_cell_or_finish_prefix
      middleActual handle request row currentCell with inherited | produced
  · obtain ⟨finishUsed, _suffixCount, beforeFinish, continuation, _total, finishSmall, _finishFuel,
        finishActual, owner, _finishEvent, _finished, _suffix⟩ :=
      SourceCurrentAllocatedNativeEdgeReturnOrigin.returned_edge_cell_finish_prefix
        machine operations (.code (.node oldRoot .pure)) oldControl oldSnapshot oldFuel oldCount
        oldBound oldActual handle request row inherited
    exact producer_edge_profiles_at_target_nodes sourceHeap entry body depth ordinary bodyCodec
      oldRoot coldInitial coldPhysical sourceGrowth operationsValid oldFuel oldCount finishUsed handle
      request row oldControl oldSnapshot beforeFinish continuation oldBound oldActual finishSmall
      finishActual owner oldInputs oldFields nextRoot middleSnapshot nextCount nodeSeed middleRetained
  · obtain ⟨finishUsed, _suffixCount, beforeFinish, continuation, total,
        finishActual, owner, _finishEvent, _finished, _suffix⟩ := produced
    exact producer_edge_profiles_at_target_nodes sourceHeap entry body depth ordinary bodyCodec
      middleRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1 oldOperations.2.2.2.2.1
      middleFuel middleCount finishUsed handle request row middleControl middleSnapshot beforeFinish continuation
      middleBound middleActual (by omega) finishActual owner middleInputs middleFields
      nextRoot middleSnapshot nextCount nodeSeed (SourceEqualityNativeDemandMemo.Retained.refl _)

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
