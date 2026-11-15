import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeOrderedMixedReferenceNodeProfile
import MicroCFTA.SourceCurrentAllocatedNativeNodeChildBeforeFinish
import MicroCFTA.SourceCurrentNativeWriterReadyRetention

/-!
# Original mixed reference and node results at one parent finish

The actual ordered entry and producer belong to the fixed whole trace.
The earlier query cache law follows from returned-cell retention.
Each completed child stays before the observed parent finish.
The same past C/M law supplies the actual returned child result.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry MixedQualified Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The actual reference/node result follows from the past C/M law at this exact finish. -/
theorem mixed_reference_node_profile_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width) rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (referenceFirst : Bool) (operandEntry : Interned NodeKey)
    (operandRows : List (EdgeValue Symbol Guard)) (operandLevel : Nat)
    (requestShape :
      request.left = (if referenceFirst then .reference (.interned entry.identity)
        else .node operandEntry operandRows operandLevel []) ∧
      request.right = (if referenceFirst then .node operandEntry operandRows operandLevel []
        else .reference (.interned entry.identity)))
    (qualified : MixedQualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request)
    (past :
      Returned (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value := by
  have originalQualified := qualified
  obtain ⟨pattern, patternId, openAlias, operand, authentic, _aliasKind,
      operandProfile, _operandHeight, strictAlias, ordered⟩ := qualified
  let reference : Node := .reference (.interned entry.identity)
  let nodeOperand : Node := .node operandEntry operandRows operandLevel []
  have notReference : operand ≠ reference := by
    intro same
    have closed := operandProfile.1
    rw [same] at closed
    cases closed
  have aliasOperand : openAlias = reference ∧ operand = nodeOperand := by
    cases referenceFirst with
    | false =>
        have leftShape : request.left = nodeOperand := requestShape.1
        have rightShape : request.right = reference := requestShape.2
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · exact False.elim (notReference (right.symm.trans rightShape))
        · exact ⟨right.symm.trans rightShape, left.symm.trans leftShape⟩
    | true =>
        have leftShape : request.left = reference := requestShape.1
        have rightShape : request.right = nodeOperand := requestShape.2
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · exact ⟨left.symm.trans leftShape, right.symm.trans rightShape⟩
        · exact False.elim (notReference (left.symm.trans leftShape))
  have nodeProfile : Profile entry.identity nodeOperand := by
    simpa only [aliasOperand.2] using operandProfile
  have nodeSmaller : height nodeOperand < height pattern := by
    simpa only [aliasOperand.2] using strictAlias aliasOperand.1
  have originalEntry := authentic
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _allocatedEq, _entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let selectedRequest : NodeRequest Symbol Guard := ⟨entered.1,
    if referenceFirst then reference else nodeOperand,
    if referenceFirst then nodeOperand else reference⟩
  have requestEq : request = selectedRequest := by
    change (⟨request.domain, request.left, request.right⟩ : NodeRequest Symbol Guard) =
      ⟨entered.1, if referenceFirst then reference else nodeOperand,
        if referenceFirst then nodeOperand else reference⟩
    rw [domainEq, requestShape.1, requestShape.2]
  subst request
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, bodyOwner, rawBody, resumeEq⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish
      rootRequest machine machineValid operations fuel finishUsed handle selectedRequest value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      ((Control.code (.node selectedRequest .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node selectedRequest .pure)) queryResume
      (⟨initial width machine, operations⟩ : Checked width) queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  have bodyPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension actualDispatch queryPhysical).1
  have queryTotal : queryUsed + (finishUsed - queryUsed) = finishUsed := by omega
  have wholeBeforeFinish : Trace (queryUsed + (finishUsed - queryUsed)) (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode handle value parentNext)) beforeFinish := by
    simpa only [queryTotal] using actual
  have querySplit := SourceCurrentHereditaryNativePhysicalSplit.split queryPrefix.steps wholeBeforeFinish
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained querySplit.2 queryPhysical.shape
  let nodeLaw := NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary
  let edgeLaw := EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary
  have priorNodes : Returned (fun old result =>
      (old = selectedRequest → Profile entry.identity result) ∧ nodeLaw old result) queryBefore.native.nodes := by
    intro cell old result storedCell
    have law := past.1 cell old result (retained.nodes cell old result storedCell)
    refine ⟨?_, law⟩
    intro same
    subst old
    exact law.2 originalQualified
  have priorEdges : Returned edgeLaw queryBefore.native.edges := by
    intro cell old result storedCell
    exact past.2 cell old result (retained.edges cell old result storedCell)
  let finished : Checked width :=
    {beforeFinish with native := SourceRecursiveIntersectionThunks.finishNode handle value beforeFinish.native}
  have finishedOne : Steps 1 (.code (.finishNode handle value (.pure value))) beforeFinish
      (.code (.pure value)) finished := .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
  have bodyLifted := rawBody.bind _ _ _ _ _ (fun result => .finishNode handle result (.pure result))
  have bodyComplete := bodyLifted.trans _ _ _ _ _ _ _ _ finishedOne
  have parentComplete : Steps (bodyCount + 2) (.code (.node selectedRequest .pure)) queryBefore
      (.code (.pure value)) finished := by
    have combined := isolatedDispatch.trans _ _ _ _ _ _ _ _ bodyComplete
    have countEq : 1 + (bodyCount + 1) = bodyCount + 2 := by omega
    simpa only [countEq] using combined
  have observedBeforeFinish : Trace (queryUsed + 1 + bodyCount) (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode handle value (queryResume value))) beforeFinish := by
    simpa only [total, resumeEq] using actual
  have producer :=
    SourceCurrentAllocatedNativeOrderedMixedReferenceNodeProfile.current_stored_universe_reference_node_profile_of_fuel_induction_ordered_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      pattern patternClosed patternId patternIdentity patternKind universeFirst
      nodeOperand operandEntry operandRows operandLevel rfl nodeProfile nodeSmaller referenceFirst
      (.code (.node rootRequest .pure)) (⟨initial width machine, operations⟩ : Checked width)
      entryBefore queryBefore reader initialPhysical sourceGrowth wholeCount entryUsed queryUsed rest
      wholeActual (by omega) entryNext entryPrefix.steps
  dsimp only at producer
  have result := producer queryResume queryOrigin nodeLaw edgeLaw (fuel - queryUsed)
    (bodyCount + 2) value finished queryPhysical queryGrowth queryOperations queryInputs queryFields
    priorNodes priorEdges (by omega) (by omega) parentComplete (by
      intro child used childFuel childCount positive _childSmaller _childFuelBound _childCountBound
        _parentSpan childCase next first middle result origin _childPhysical _childGrowth
        _childOperations _childInputs _childFields _childNodes _childEdges
        _leftAvailable _rightAvailable childActual
      have childQualified : Qualified (width := width) rootRequest machine operations wholeCount
          entry body depth ordinary child := by
        rcases childCase with ⟨_same, leftProfile, rightProfile, nonempty⟩ | same
        · exact Or.inl ⟨leftProfile, rightProfile, Or.inr nonempty⟩
        · subst child
          exact Or.inr ⟨pattern, patternId, reference, nodeOperand,
            originalEntry, Or.inr rfl, nodeProfile, Nat.le_of_lt nodeSmaller,
            (fun _ => nodeSmaller), Or.inr ⟨rfl, rfl⟩⟩
      obtain ⟨childKey, keyed⟩ := SourceCurrentAllocatedNativeGeneralCMHistory.qualified_key
        rootRequest machine operations wholeCount entry body depth ordinary bodyCodec child childQualified
      have span := SourceCurrentAllocatedNativeNodeChildBeforeFinish.completed_node_child_span_before_parent_finish
        (.code (.node rootRequest .pure)) queryResume selectedRequest child handle
        (⟨initial width machine, operations⟩ : Checked width) queryBefore beforeBody beforeFinish first middle
        (fuel - queryUsed) bodyCount queryUsed used childCount value result next
        bodyPhysical.shape bodyOwner (by omega) observedBeforeFinish queryOrigin isolatedDispatch rawBody
        positive origin childActual
      obtain ⟨_localSpan, globalSpan, _suppliedSpan, _owner, _returnedOwner,
        childPrefix, _checkedChild, _childEnd, _childSuffix⟩ := span
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
        nodeLaw edgeLaw rootRequest machine machineValid operations fuel finishUsed (queryUsed + used) childCount
        handle value parentNext beforeFinish (by omega) actual past child childKey keyed
        (fun result => (next result).bind queryResume) first middle result (by omega) childPrefix.steps childActual
      rcases childQualified with closed | mixed
      · exact currentLaw.1.1 closed
      · exact currentLaw.1.2 mixed)
  exact result.1

end MicroCFTA.SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish

#check MicroCFTA.SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish.mixed_reference_node_profile_at_actual_node_finish
#print axioms MicroCFTA.SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish.mixed_reference_node_profile_at_actual_node_finish
