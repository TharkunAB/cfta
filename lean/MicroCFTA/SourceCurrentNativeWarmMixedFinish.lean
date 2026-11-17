import MicroCFTA.SourceCurrentAllocatedNativeGeneralMNodeFinish
import MicroCFTA.SourceCurrentNativeWarmCMDefinitions
import MicroCFTA.SourceCurrentNativeWarmAuxiliaryPrefixes

namespace MicroCFTA.SourceCurrentNativeWarmMixedFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision payload identity tag pair)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
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

/- Note [Mixed results on the actual warm history]
The actual root trace starts at the same warm snapshot throughout.
Each child result is read at the observed parent before-finish state.
The source wrapper derives all four auxiliary cache laws at that prefix.
The original full pattern and the fixed full history remain unchanged.
-/

private theorem closed_codec (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem key_of_codecs {width : Nat} (request : NodeRequest Symbol Guard)
    (left : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (right : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  obtain ⟨first, firstInput⟩ := left
  obtain ⟨second, secondInput⟩ := right
  exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    first second firstInput secondInput⟩

private theorem warm_qualified_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (request : NodeRequest Symbol Guard)
    (qualified : Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases qualified with closed | mixed
  · exact key_of_codecs (width := width) request (closed_codec _ closed.1.1) (closed_codec _ closed.2.1.1)
  · obtain ⟨pattern, patternId, openAlias, operand, _authentic, alias, operandProfile,
      _height, _strict, ordered⟩ := mixed
    have aliasCodec : ∃ input, IntersectionFlatMemoKey.input openAlias.referenceOf = some input := by
      rcases alias with rfl | rfl
      · exact bodyCodec
      · exact ⟨.ref entry.identity, rfl⟩
    have operandCodec := closed_codec _ operandProfile.1
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact key_of_codecs (width := width) request (by rw [left]; exact aliasCodec) (by rw [right]; exact operandCodec)
    · exact key_of_codecs (width := width) request (by rw [left]; exact operandCodec) (by rw [right]; exact aliasCodec)


namespace Ordinary

open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
  (ordinary_payload ordinary_code make_node_profile all₂_row_profiles)

set_option autoImplicit false

private theorem ordinary_nodes (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    (∃ (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference),
      request.left = .node entry rows depth free) ∧
    (∃ (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference),
      request.right = .node entry rows depth free) := by
  have chosen := ordinary_payload request selected
  cases left : request.left <;> cases right : request.right <;>
    simp only [left, right, SourceRecursiveIntersectionControl.payload] at chosen <;> try cases chosen
  exact ⟨⟨_, _, _, _, rfl⟩, ⟨_, _, _, _, rfl⟩⟩

/-- The original mixed ordinary result follows from the past law at this exact finish. -/
private theorem mixed_ordinary_profile_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary request)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value := by
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle request value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.node request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node request .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  obtain ⟨_checkedDispatch, bodyPhysical, _bodyExtension, bodyGrowth, bodyOperations,
      _bodyOperationsGrowth, _bodyBoundInputs, bodyInputs, _bodyBoundFields, bodyFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      (fuel - queryUsed) 1 (.code (.node request .pure)) (.code (compileNode request))
      (fun result => .finishNode handle result (.pure result)) queryBefore beforeBody sourceHeap
      queryPhysical queryInputs queryFields queryOperations queryGrowth isolatedDispatch (by omega)
  obtain ⟨bodyTrace, _finishPhysical, _finishExtension, _finishGrowth, _finishOperations,
      _finishOperationsGrowth, _finishBoundInputs, _finishInputs, _finishBoundFields, _finishFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      ((fuel - queryUsed) - 1) bodyCount (.code (compileNode request)) (.code (.pure value)) .pure
      beforeBody beforeFinish sourceHeap bodyPhysical bodyInputs bodyFields bodyOperations bodyGrowth rawBody (by omega)
  obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
      operandProfile, operandHeight, _strictAlias, ordered⟩ := qualified
  obtain ⟨leftNode, rightNode⟩ := ordinary_nodes request selected
  have aliasNode : ∃ (input : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List Reference), openAlias = .node input rows depth free := by
    rcases ordered with ⟨left, _⟩ | ⟨_, right⟩
    · simpa only [left] using leftNode
    · simpa only [right] using rightNode
  have aliasBody : openAlias = body := by
    rcases aliasKind with same | reference
    · exact same
    · obtain ⟨input, rows, nodeDepth, free, impossible⟩ := aliasNode
      rw [reference] at impossible
      cases impossible
  subst openAlias
  have operandNode : ∃ (input : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
      (depth : Nat) (free : List Reference), operand = .node input rows depth free := by
    rcases ordered with ⟨_, right⟩ | ⟨left, _⟩
    · simpa only [right] using rightNode
    · simpa only [left] using leftNode
  obtain ⟨operandEntry, operandRows, operandDepth, operandFree, rfl⟩ := operandNode
  have operandAvailable : Available queryBefore.native.machine.heap
      (.node operandEntry operandRows operandDepth operandFree) := by
    rcases ordered with ⟨_, right⟩ | ⟨left, _⟩
    · simpa only [right] using queryReady.2.2
    · simpa only [left] using queryReady.2.1
  obtain ⟨bodyFirst, leftEq, rightEq⟩ :
      ∃ bodyFirst : Bool,
        request.left = (if bodyFirst then body else .node operandEntry operandRows operandDepth operandFree) ∧
        request.right = (if bodyFirst then .node operandEntry operandRows operandDepth operandFree else body) := by
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact ⟨true, left, right⟩
    · exact ⟨false, left, right⟩
  have originalEntry := authentic
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _allocatedEq, entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let enteredAfter : Checked width :=
    {entryBefore with native := advance entryBefore.native {entryBefore.native.machine with domains := entered.2}}
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have wholeForEntry : Trace (entryUsed + (wholeCount - entryUsed)) (.code (.node rootRequest .pure))
      start rest reader := by
    simpa only [entryTotal] using wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps wholeForEntry
  have eventTotal : 1 + (wholeCount - entryUsed - 1) = wholeCount - entryUsed := by omega
  have eventRemainder : Trace (1 + (wholeCount - entryUsed - 1))
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then universeValue else pattern)
        (if universeFirst then pattern else universeValue)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore rest reader := by
    simpa only [eventTotal] using entrySplit.2
  have eventSplit := SourceCurrentHereditaryNativePhysicalSplit.split entryOne.steps eventRemainder
  have sourceChildren :=
    SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification.current_stored_universe_mixed_ordinary_child_qualification_ordered_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      pattern patternClosed patternId patternIdentity patternKind universeFirst
      (.code (.node rootRequest .pure)) start
      entryBefore enteredAfter initialPhysical sourceGrowth entryUsed entryNext entrySplit.1
  dsimp only at sourceChildren
  obtain ⟨_patternAvailable, _enteredDomain, nonempty, bodyEntry, bodyRows, marker,
      bodyShape, _markerClosed, _markerAtoms, eachAt⟩ := sourceChildren eventSplit.1
  have domainNonempty : request.domain.key.free.isEmpty = false := by
    rw [domainEq]
    exact nonempty
  have leftRows : InternedEdgeResidency.nodeEdges request.left =
      (if bodyFirst then bodyRows else operandRows) := by
    rw [leftEq]
    cases bodyFirst with
    | false => rfl
    | true => exact congrArg InternedEdgeResidency.nodeEdges bodyShape
  have rightRows : InternedEdgeResidency.nodeEdges request.right =
      (if bodyFirst then operandRows else bodyRows) := by
    rw [rightEq]
    cases bodyFirst with
    | false => exact congrArg InternedEdgeResidency.nodeEdges bodyShape
    | true => rfl
  have originalPairsQualified :
      ∀ pair ∈ pairs (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right),
      ∀ children ∈ pair.1.children.zip pair.2.children,
        Qualified (width := width) rootRequest start wholeCount entry body depth ordinary
          ⟨request.domain, children.1, children.2⟩ := by
    intro pair matched children included
    have sourceMatched : pair ∈ pairs
        (if bodyFirst then bodyRows else operandRows) (if bodyFirst then operandRows else bodyRows) := by
      simpa only [leftRows, rightRows] using matched
    have details := (eachAt queryBefore queryPhysical operandEntry operandRows operandDepth operandFree
      operandAvailable operandProfile operandHeight bodyFirst pair sourceMatched).1 children included
    rcases details.2.2.2 with closed | referenceLeft | referenceRight
    · exact Or.inl ⟨closed.1, closed.2, Or.inr domainNonempty⟩
    · exact Or.inr ⟨pattern, patternId, .reference (.interned entry.identity), children.2,
        originalEntry, Or.inr rfl, referenceLeft.2.1, Nat.le_of_lt referenceLeft.2.2,
        (fun _ => referenceLeft.2.2), Or.inl ⟨referenceLeft.1, rfl⟩⟩
    · exact Or.inr ⟨pattern, patternId, .reference (.interned entry.identity), children.1,
        originalEntry, Or.inr rfl, referenceRight.2.1, Nat.le_of_lt referenceRight.2.2,
        (fun _ => referenceRight.2.2), Or.inr ⟨rfl, referenceRight.1⟩⟩
  have compiled := ordinary_code request selected
  have rowsTrace : Trace bodyCount
      (.code (compileRows request.domain (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right))) beforeBody
      (.code (.pure value)) beforeFinish := by
    rw [← compiled]
    exact bodyTrace
  let finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun result => .finishNode handle result (queryResume result)
  have bodyStart : Steps (queryUsed + 1) (.code (.node rootRequest .pure))
      start
      (.code ((compileNode request).bind finishNext)) beforeBody := by
    simpa only [finishNext] using queryPrefix.steps.trans _ _ _ _ _ _ _ _ actualDispatch.steps
  have observed := SourceCurrentAllocatedNativeRowsPhysicalReadback.compile_rows_physical_readback_of_smaller_edges
    request.domain (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right) beforeBody beforeFinish
    (bodyCount + 1) bodyCount value
    (fun (_pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (row : EdgeValue Symbol Guard) =>
      ∀ child ∈ row.children, Profile entry.identity child)
    bodyPhysical (trace_done bodyCount _ beforeBody beforeFinish value rowsTrace.steps) rowsTrace (by
      intro stepsBefore childFuel room _childSmaller pair member next first last row origin childPhysical childDone
      obtain ⟨rawCount, rawSmaller, rawSteps⟩ := done_trace childFuel _ first last row childDone
      have localSpan : stepsBefore + rawCount ≤ bodyCount := by omega
      let lifted : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun result => (next result).bind finishNext
      have bodyPrefix : Steps stepsBefore (.code (compileNode request)) beforeBody
          (.code ((requestEdge request.domain pair.1 pair.2).bind next)) first := by
        rw [compiled]
        exact origin
      have appended := bodyPrefix.bind _ _ _ _ _ finishNext
      have outer : Steps ((queryUsed + 1) + stepsBefore) (.code (.node rootRequest .pure))
          start
          (.code ((requestEdge request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Control.bind, Code.bind_assoc, lifted] using bodyStart.trans _ _ _ _ _ _ _ _ appended
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixEdgeChildResult.edge_child_law_at_actual_warm_reader
        (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        rootRequest start initialPhysical fuel finishUsed ((queryUsed + 1) + stepsBefore) rawCount
        (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual past
        ⟨request.domain, pair.1, pair.2⟩ lifted first last row (by omega) outer rawSteps
      obtain ⟨_remaining, _total, _checkedPrefix, atQuery⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix origin rowsTrace
      obtain ⟨_rest, _length, boundQuery, _remainingTrace⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix
          (rawSteps.bind _ _ _ _ _ next) atQuery
      have rawChecked := SourceCurrentHereditaryNativePhysicalSplit.unbind rawSteps next boundQuery
      exact ⟨currentLaw.1 (originalPairsQualified pair member),
        SourceCurrentAllocatedNativeRequestResults.edge_result rawCount
          ⟨request.domain, pair.1, pair.2⟩ first last row childPhysical rawChecked⟩)
  obtain ⟨rows, middle, _count, _countBound, _walked, aligned, middlePhysical,
      _middleExtension, resident, _throughWork, resultEq, _afterEq, _canonical,
      _free, _afterPhysical, _afterExtension, _available, _afterResident⟩ := observed
  rw [resultEq]
  exact make_node_profile entry.identity rows middle.native.machine.heap middlePhysical.machine.1
    resident (all₂_row_profiles entry.identity aligned)

end Ordinary

namespace Union

open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)

set_option autoImplicit false

private theorem mixed_union_profile_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (unionOperand : ∃ (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference),
      request.left = .union unionEntry members level free ∨
        request.right = .union unionEntry members level free)
    (qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary request)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value := by
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle request value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.node request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node request .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  obtain ⟨_checkedDispatch, bodyPhysical, _bodyExtension, bodyGrowth, bodyOperations,
      _bodyOperationsGrowth, _bodyBoundInputs, bodyInputs, _bodyBoundFields, bodyFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      (fuel - queryUsed) 1 (.code (.node request .pure)) (.code (compileNode request))
      (fun result => .finishNode handle result (.pure result)) queryBefore beforeBody sourceHeap
      queryPhysical queryInputs queryFields queryOperations queryGrowth isolatedDispatch (by omega)
  obtain ⟨bodyTrace, _finishPhysical, _finishExtension, _finishGrowth, _finishOperations,
      _finishOperationsGrowth, _finishBoundInputs, _finishInputs, _finishBoundFields, _finishFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      ((fuel - queryUsed) - 1) bodyCount (.code (compileNode request)) (.code (.pure value)) .pure
      beforeBody beforeFinish sourceHeap bodyPhysical bodyInputs bodyFields bodyOperations bodyGrowth rawBody (by omega)
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _sourceFacts⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  obtain ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
      operandProfile, operandHeight, strictAlias, ordered⟩ := qualified
  obtain ⟨unionEntry, members, level, free, unionSide⟩ := unionOperand
  have aliasNotUnion : openAlias ≠ .union unionEntry members level free := by
    rcases aliasKind with same | same
    · rw [same, bodyEq]
      intro impossible
      cases impossible
    · rw [same]
      intro impossible
      cases impossible
  have operandEq : operand = .union unionEntry members level free := by
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · rcases unionSide with same | same
      · exact (aliasNotUnion (left.symm.trans same)).elim
      · exact right.symm.trans same
    · rcases unionSide with same | same
      · exact left.symm.trans same
      · exact (aliasNotUnion (right.symm.trans same)).elim
  subst operand
  obtain ⟨useReference, aliasEq⟩ : ∃ useReference : Bool,
      openAlias = (if useReference then .reference (.interned entry.identity) else body) := by
    rcases aliasKind with same | same
    · exact ⟨false, same⟩
    · exact ⟨true, same⟩
  let alias : Node := if useReference then .reference (.interned entry.identity) else body
  have aliasChoice : alias = body ∨ alias = .reference (.interned entry.identity) := by
    cases useReference with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  have orderedAlias :
      ((request.left = alias ∧ request.right = .union unionEntry members level free) ∨
        (request.left = .union unionEntry members level free ∧ request.right = alias)) := by
    simpa only [aliasEq] using ordered
  obtain ⟨aliasFirst, leftEq, rightEq⟩ : ∃ aliasFirst : Bool,
      request.left = (if aliasFirst then alias else .union unionEntry members level free) ∧
      request.right = (if aliasFirst then .union unionEntry members level free else alias) := by
    rcases orderedAlias with ⟨left, right⟩ | ⟨left, right⟩
    · exact ⟨true, left, right⟩
    · exact ⟨false, left, right⟩
  have referenceBound : useReference = true →
      height (.union unionEntry members level free) < height pattern := by
    intro used
    apply strictAlias
    rw [aliasEq, used]
    rfl
  have originalEntry := authentic
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, allocationEq, _entryOne, domainEq⟩ := entryData
  let universeValue : Node := .mu entry body depth ordinary
  let actualEntered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey
    (if universeFirst then universeValue else pattern)
    (if universeFirst then pattern else universeValue)
    (if universeFirst then entry.identity else patternId)
    (if universeFirst then patternId else entry.identity)
  have domainOrdered : request.domain = actualEntered.1 :=
    domainEq.trans (congrArg Prod.fst allocationEq).symm
  let desired : NodeRequest Symbol Guard := ⟨actualEntered.1,
    if aliasFirst then alias else .union unionEntry members level free,
    if aliasFirst then .union unionEntry members level free else alias⟩
  have requestEq : request = desired := by
    cases request with
    | mk domain left right =>
        change domain = actualEntered.1 at domainOrdered
        change left = _ at leftEq
        change right = _ at rightEq
        simp only [desired, domainOrdered, leftEq, rightEq]
  subst request
  have raw := SourceCurrentAllocatedNativeMixedUnionProfile.current_stored_universe_mixed_union_body_profile_of_fuel_induction
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    pattern patternClosed patternId patternIdentity patternKind
    unionEntry members level free operandProfile operandHeight useReference aliasFirst universeFirst referenceBound
    (.code (.node rootRequest .pure)) start
    entryBefore queryBefore beforeBody reader initialPhysical sourceGrowth
    wholeCount entryUsed queryUsed rest wholeActual (by omega) entryNext entryPrefix.steps
  dsimp only at raw
  refine (raw queryResume queryOrigin (fuel - queryUsed) bodyCount value beforeFinish
    (fun emitted => .finishNode handle emitted (.pure emitted))
    queryOperations queryInputs queryFields isolatedDispatch (by omega) (by omega) rawBody ?_).1
  intro closedOperand child used childFuel childCount _positive _smaller _fuelSpan
    _rawSmaller actualSpan childDomain ownProfile childHeight strictChild orderedChild
    next first last emitted origin _childPhysical _childGrowth _childOperations _childInputs
    _childFields _leftAvailable _rightAvailable childActual
  have childQualified : MixedQualifiedAt (width := width) rootRequest start wholeCount
      entry body depth ordinary child := by
    refine ⟨pattern, patternId, alias, closedOperand, ?_, aliasChoice, ownProfile,
      childHeight, strictChild, orderedChild⟩
    rw [childDomain]
    exact originalEntry
  obtain ⟨childKey, keyed⟩ := warm_qualified_key
    rootRequest start wholeCount entry body depth ordinary bodyCodec child (Or.inr childQualified)
  have lifted := origin.bind _ _ _ _ _ queryResume
  have globalOrigin : Steps (queryUsed + used) (.code (.node rootRequest .pure))
      start
      (.code ((requestNode child.domain child.left child.right).bind
        (fun result => (next result).bind queryResume))) first := by
    simpa only [Control.bind, Code.bind_assoc] using
      queryOrigin.trans _ _ _ _ _ _ _ _ lifted
  have observed := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
    (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
    (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
    rootRequest start initialPhysical fuel finishUsed (queryUsed + used) childCount
    (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual past child childKey keyed
    (fun result => (next result).bind queryResume) first last emitted (by omega) globalOrigin childActual
  exact observed.1.2 childQualified

end Union

namespace ReferenceNode

open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)

set_option autoImplicit false

/-- The actual reference/node result follows from the past C/M law at this exact finish. -/
private theorem mixed_reference_node_profile_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (referenceFirst : Bool) (operandEntry : Interned NodeKey)
    (operandRows : List (EdgeValue Symbol Guard)) (operandLevel : Nat)
    (requestShape :
      request.left = (if referenceFirst then .reference (.interned entry.identity)
        else .node operandEntry operandRows operandLevel []) ∧
      request.right = (if referenceFirst then .node operandEntry operandRows operandLevel []
        else .reference (.interned entry.identity)))
    (qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary request)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
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
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, bodyOwner, rawBody, resumeEq⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle selectedRequest value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.node selectedRequest .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node selectedRequest .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  have bodyPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension actualDispatch queryPhysical).1
  have queryTotal : queryUsed + (finishUsed - queryUsed) = finishUsed := by omega
  have wholeBeforeFinish : Trace (queryUsed + (finishUsed - queryUsed)) (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish := by
    simpa only [queryTotal] using actual
  have querySplit := SourceCurrentHereditaryNativePhysicalSplit.split queryPrefix.steps wholeBeforeFinish
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained querySplit.2 queryPhysical.shape
  let nodeLaw := NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary
  let edgeLaw := EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary
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
      start
      (.code (.finishNode handle value (queryResume value))) beforeFinish := by
    simpa only [total, resumeEq] using actual
  have producer :=
    SourceCurrentAllocatedNativeOrderedMixedReferenceNodeProfile.current_stored_universe_reference_node_profile_of_fuel_induction_ordered_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      pattern patternClosed patternId patternIdentity patternKind universeFirst
      nodeOperand operandEntry operandRows operandLevel rfl nodeProfile nodeSmaller referenceFirst
      (.code (.node rootRequest .pure)) start
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
      have childQualified : Qualified (width := width) rootRequest start wholeCount
          entry body depth ordinary child := by
        rcases childCase with ⟨_same, leftProfile, rightProfile, nonempty⟩ | same
        · exact Or.inl ⟨leftProfile, rightProfile, Or.inr nonempty⟩
        · subst child
          exact Or.inr ⟨pattern, patternId, reference, nodeOperand,
            originalEntry, Or.inr rfl, nodeProfile, Nat.le_of_lt nodeSmaller,
            (fun _ => nodeSmaller), Or.inr ⟨rfl, rfl⟩⟩
      obtain ⟨childKey, keyed⟩ := warm_qualified_key
        rootRequest start wholeCount entry body depth ordinary bodyCodec child childQualified
      have span := SourceCurrentAllocatedNativeNodeChildBeforeFinish.completed_node_child_span_before_parent_finish
        (.code (.node rootRequest .pure)) queryResume selectedRequest child handle
        start queryBefore beforeBody beforeFinish first middle
        (fuel - queryUsed) bodyCount queryUsed used childCount value result next
        bodyPhysical.shape bodyOwner (by omega) observedBeforeFinish queryOrigin isolatedDispatch rawBody
        positive origin childActual
      obtain ⟨_localSpan, globalSpan, _suppliedSpan, _owner, _returnedOwner,
        childPrefix, _checkedChild, _childEnd, _childSuffix⟩ := span
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
        nodeLaw edgeLaw rootRequest start initialPhysical fuel finishUsed (queryUsed + used) childCount
        (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual past child childKey keyed
        (fun result => (next result).bind queryResume) first middle result (by omega) childPrefix.steps childActual
      rcases childQualified with closed | mixed
      · exact currentLaw.1.1 closed
      · exact currentLaw.1.2 mixed)
  exact result.1

end ReferenceNode

namespace BodyFirstOuter

open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

set_option autoImplicit false

private theorem mu_code [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .rightMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

private theorem optional_reclosed_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (binder : Nat × Nat) (product expected : Value Symbol Guard)
    (before after : Checked width) (count : Nat) (result : Value Symbol Guard)
    (one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder product .pure)) before =
      .yielded (.code (.pure expected)) before)
    (actual : Steps count (.code (.optionalBinder binder product .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = expected ∧ after = before := by
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      have same := Outcome.yielded.inj (chosen.symm.trans one)
      rw [same.1, same.2] at tail
      have terminal := pure_trace remaining expected result before after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- The actual body-first parent uses its returned child at the same finish. -/
private theorem body_first_outer_finish_of_past_body_first_key_law
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (fuel wholeCount finishCount : Nat)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
    (sameKey : actualDomain.key = domain.key)
    (parentHandle : Nat) (value : Value Symbol Guard)
    (rest : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start readerControl reader)
    (finishWithin : finishCount + 1 ≤ wholeCount)
    (actual : Trace finishCount (.code (.node rootRequest .pure))
      start
      (.code (.finishNode parentHandle value rest)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells parentHandle =
      some ⟨⟨actualDomain, body, .mu entry body depth ordinary⟩, .evaluating⟩)
    (plan : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (past : Returned
      (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId (extend domain.key [entry.identity] (pair bodyId entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes) :
    value = .mu entry body depth ordinary := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let initialState : Checked width := start
  let rootControl : Control (Value Symbol Guard) := .code (.node rootRequest .pure)
  let request : NodeRequest Symbol Guard := ⟨actualDomain, body, universeValue⟩
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical
  have readerGrowth : Grows sourceHeap reader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth atReader.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed, entryBefore,
    entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _orderedTuple, _entryOne, domainEq⟩ := entryData
  let entryLeft := if universeFirst then universeValue else pattern
  let entryRight := if universeFirst then pattern else universeValue
  let firstId := if universeFirst then entry.identity else patternId
  let secondId := if universeFirst then patternId else entry.identity
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  change domain = sourceDomain.1 at domainEq
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have entryWhole : Trace (entryUsed + (wholeCount - entryUsed)) rootControl initialState readerControl reader :=
    entryTotal.symm ▸ wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps entryWhole
  have entryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 initialPhysical
  have entryLength : wholeCount - entryUsed = (wholeCount - entryUsed - 1) + 1 := by omega
  have entryActual : Trace ((wholeCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext))
      entryBefore readerControl reader := entryLength ▸ entrySplit.2
  obtain ⟨_entryStep, _entryTail, _entryHeap, _entryDomains, _entryOperations, _oldDomain,
    _leftAtEntry, _rightAtEntry, leftReader, rightReader, _domainAfterEntry, _domainAtReader,
    _enteredKey, _entryExtension, _sameRecord⟩ :=
    SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
      IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext
      (wholeCount - entryUsed - 1) entryBefore reader readerControl entryPhysical.1 entryActual
  have patternReader : Available reader.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  have bodyIdEq : bodyEntry.identity = bodyId := by
    have observed : identity body = some bodyEntry.identity := by
      simp only [bodyShape, identity]
    exact Option.some.inj (observed.symm.trans bodyIdentity)
  subst bodyId
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  dsimp only at sourceFacts
  obtain ⟨_bodyRead, _universeRead, _bodyOpen, _cutoffApart, incomingFacts, _terminalFacts⟩ := sourceFacts
  have bodySelected : decision diagonalFirst.1.key body universeValue = .rightMu :=
    (incomingFacts diagonalFirst.1 rfl).1
  have sourceValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.1.machine.2 _).1
  have diagonalKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceValid sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  have tagOrder : compare (1 : Nat) 2 = .lt := by decide
  have bodyDiagonalFresh : pair bodyEntry.identity entry.identity ∉ diagonalFirst.1.key.seen := by
    intro member
    have repeated : decision diagonalFirst.1.key body universeValue =
        .repeated (pair bodyEntry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        bodyShape, universeValue, Value.referenceOf, Value.free, member, tagOrder]
    rw [repeated] at bodySelected
    cases bodySelected
  have sourceFresh : pair bodyEntry.identity entry.identity ∉ sourceDomain.1.key.seen := by
    intro member
    apply bodyDiagonalFresh
    rw [diagonalKey]
    exact (extend_seen _ _ _ _).mpr (Or.inr member)
  have sourceSameKey : actualDomain.key = sourceDomain.1.key :=
    sameKey.trans (congrArg (fun current => current.key) domainEq)
  have actualFresh : pair bodyEntry.identity entry.identity ∉ actualDomain.key.seen := by
    rw [sourceSameKey]
    exact sourceFresh
  have selected : decision request.domain.key request.left request.right = .rightMu := by
    simp [request, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      bodyShape, universeValue, Value.referenceOf, Value.free, actualFresh, tagOrder]
  have compiled := mu_code request selected
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, total, _queryBeforeFinish, _queryBound,
    queryPrefix, dispatched, _isolated, queryPhysical, _queryReady, _querySafe, _bodyOwner, bodyActual, _resumeEq⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishCount parentHandle request value rest
      beforeFinish (by omega) actual owner
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension dispatched queryPhysical).1
  let allocated := SourceRecursiveIntersectionEnvironment.enter beforeBody.native.machine.domains request.domain.key
    request.left request.right bodyEntry.identity entry.identity
  let started : Checked width :=
    {beforeBody with native := advance beforeBody.native {beforeBody.native.machine with domains := allocated.2}}
  let binder := pair bodyEntry.identity entry.identity
  let childCode := requestNode allocated.1 body body
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => .optionalBinder binder product .pure
  let finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun result => .finishNode parentHandle result (resume result)
  let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => (next product).bind finishNext
  have bodyRead : identity request.left = some bodyEntry.identity := by
    simp only [request, bodyShape, identity]
  have one : step (.code (compileNode request)) beforeBody =
      .yielded (.code (childCode.bind next)) started := by
    rw [compiled]
    have receipt := SourceCurrentAllocatedNativeMuSource.enter_prefix request beforeBody
      bodyEntry.identity entry.identity bodyRead rfl
    simpa only [childCode, requestNode, Code.bind, next, binder, started, allocated,
      request, universeValue, bodyShape, SourceRecursiveIntersectionKernel.body] using receipt
  have bodyEnter : Steps 1 (.code (compileNode request)) beforeBody
      (.code (childCode.bind next)) started := .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have names : (SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst =
      [entry.identity] := by
    simp only [request, bodyShape, universeValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder, List.nil_append, List.map_cons, List.map_nil]
  have keyCalculation := SourceRecursiveIntersectionSchedule.entered_key beforeBody.native.machine.domains
    beforePhysical.machine.2 request.domain.key request.left request.right bodyEntry.identity entry.identity
  change allocated.1.key = extend request.domain.key
    ((SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst)
    (pair bodyEntry.identity entry.identity) at keyCalculation
  have allocatedKey : allocated.1.key =
      extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) := by
    have normalized : allocated.1.key = extend actualDomain.key [entry.identity]
        (pair bodyEntry.identity entry.identity) :=
      keyCalculation.trans (congrArg
        (fun bindings => extend request.domain.key bindings (pair bodyEntry.identity entry.identity)) names)
    exact normalized.trans (congrArg
      (fun current => extend current [entry.identity] (pair bodyEntry.identity entry.identity)) sameKey)
  have liftedBody := bodyEnter.bind _ _ _ _ _ finishNext
  have rootBody := queryPrefix.steps.trans _ _ _ _ _ _ _ _ dispatched.steps
  have intoChild := rootBody.trans _ _ _ _ _ _ _ _ liftedBody
  have childOrigin : Steps (queryUsed + 2) rootControl initialState
      (.code (childCode.bind lifted)) started := by
    simpa only [Control.bind, Code.bind_assoc, Code.bind, finishNext, lifted, Nat.add_assoc] using intoChild
  cases bodyCount with
  | zero =>
      have impossible := steps_zero _ _ _ _ bodyActual
      rw [impossible.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ bodyActual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childCount, optionalCount, product, middle, splitCount, childActual, optionalActual⟩ :=
        steps_bind_inverse remaining (.code childCode) next started beforeFinish value tail
      have keyed : ∃ key, SourceRecursiveIntersectionMemo.requestKey width allocated.1 body body = some key := by
        rw [bodyShape]
        exact ⟨_, rfl⟩
      obtain ⟨childKey, childKeyEq⟩ := keyed
      have edgeTrue : Returned (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
          beforeFinish.native.edges := by
        intro cell request result stored
        trivial
      have childPast := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
        (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult entry.identity bodyEntry.identity
          (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity)) body universeValue)
        (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
        rootRequest start initialPhysical fuel finishCount (queryUsed + 2) childCount
        (.code (.finishNode parentHandle value rest)) beforeFinish (by omega) actual ⟨past, edgeTrue⟩
        ⟨allocated.1, body, body⟩ childKey childKeyEq lifted started middle product
        (by omega) childOrigin childActual
      have shape : SourceCurrentAllocatedNativeCoherentOpenBodyResult.ProductShape
          entry.identity bodyEntry.identity entry.identity body product :=
        childPast.1.2.2.2 allocatedKey rfl rfl
      have childResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        fuel (queryUsed + 2) rootControl (.code childCode) lifted initialState started
        sourceHeap initialPhysical plan fields operationsValid sourceGrowth childOrigin (by omega)
      obtain ⟨_checkedOrigin, childPhysical, _childExtension, childGrowth, _childOperations,
        _childOperationsGrowth, _boundChildPlan, childPlan, _boundChildFields, _childFields⟩ := childResources
      have atEnd := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        (fuel - (queryUsed + 2)) childCount (.code childCode) (.code (.pure product)) .pure
        started middle childPhysical childPlan childActual (by omega)
      have middleGrowth : Grows sourceHeap middle.native.machine.heap :=
        InternedConstructorTemplates.grows_trans childGrowth atEnd.2.2.1.heap
      have available : Available middle.native.machine.heap product :=
        SourceCurrentNativeOpenRequestResults.node_result childCount
          ⟨allocated.1, body, body⟩ started middle product childPhysical atEnd.1
      obtain ⟨_reclosed, optionalOne, _optionalDone⟩ :=
        SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          middle atEnd.2.1.machine.1 middleGrowth bodyEntry.identity entry.identity product available shape
      exact (optional_reclosed_trace binder product universeValue middle beforeFinish optionalCount value
        optionalOne optionalActual).2.1

end BodyFirstOuter

namespace DiagonalOuter

open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

set_option autoImplicit false

private theorem mu_code [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .leftMu) :
    compileNode request = compileMu request.domain request.left request.right := by
  simp only [compileNode, selected]

private theorem optional_reclosed_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (binder : Nat × Nat) (product expected : Value Symbol Guard)
    (before after : Checked width) (count : Nat) (result : Value Symbol Guard)
    (one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder product .pure)) before =
      .yielded (.code (.pure expected)) before)
    (actual : Steps count (.code (.optionalBinder binder product .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = expected ∧ after = before := by
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      have same := Outcome.yielded.inj (chosen.symm.trans one)
      rw [same.1, same.2] at tail
      have terminal := pure_trace remaining expected result before after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- The actual diagonal parent uses its returned B/R child at the same finish. -/
private theorem diagonal_outer_finish_of_past_coherent_laws
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (fuel wholeCount finishCount : Nat)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain)
    (sameKey : actualDomain.key = domain.key)
    (parentHandle : Nat) (value : Value Symbol Guard)
    (rest : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (readerControl : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start readerControl reader)
    (finishWithin : finishCount + 1 ≤ wholeCount)
    (actual : Trace finishCount (.code (.node rootRequest .pure))
      start
      (.code (.finishNode parentHandle value rest)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells parentHandle =
      some ⟨⟨actualDomain, .mu entry body depth ordinary,
        .reference (.interned entry.identity)⟩, .evaluating⟩)
    (plan : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (past :
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity
        (extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
          [entry.identity] (pair bodyId entry.identity))
        (extend domain.key [entry.identity] (pair entry.identity entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult beforeFinish.native.edges) :
    value = .mu entry body depth ordinary := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let initialState : Checked width := start
  let rootControl : Control (Value Symbol Guard) := .code (.node rootRequest .pure)
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let request : NodeRequest Symbol Guard := ⟨actualDomain, universeValue, referenceValue⟩
  have atReader := SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical
  have readerGrowth : Grows sourceHeap reader.native.machine.heap :=
    InternedConstructorTemplates.grows_trans sourceGrowth atReader.2.heap
  obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst, entryUsed, entryBefore,
    entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _orderedTuple, _entryOne, domainEq⟩ := entryData
  let entryLeft := if universeFirst then universeValue else pattern
  let entryRight := if universeFirst then pattern else universeValue
  let firstId := if universeFirst then entry.identity else patternId
  let secondId := if universeFirst then patternId else entry.identity
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  change domain = sourceDomain.1 at domainEq
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have entryWhole : Trace (entryUsed + (wholeCount - entryUsed)) rootControl initialState readerControl reader :=
    entryTotal.symm ▸ wholeActual
  have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps entryWhole
  have entryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entrySplit.1 initialPhysical
  have entryLength : wholeCount - entryUsed = (wholeCount - entryUsed - 1) + 1 := by omega
  have entryActual : Trace ((wholeCount - entryUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext))
      entryBefore readerControl reader := entryLength ▸ entrySplit.2
  obtain ⟨_entryStep, _entryTail, _entryHeap, _entryDomains, _entryOperations, _oldDomain,
    _leftAtEntry, _rightAtEntry, leftReader, rightReader, _domainAfterEntry, _domainAtReader,
    _enteredKey, _entryExtension, _sameRecord⟩ :=
    SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
      IntersectionEmptyDomain.emptyDomain entryLeft entryRight firstId secondId entryNext
      (wholeCount - entryUsed - 1) entryBefore reader readerControl entryPhysical.1 entryActual
  have patternReader : Available reader.native.machine.heap pattern := by
    cases universeFirst with
    | false => exact leftReader
    | true => exact rightReader
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      reader.native.machine.heap atReader.1.machine.1 readerGrowth
      entryBefore.native.machine.domains entryPhysical.1.machine.2
      pattern patternReader patternClosed patternId patternIdentity patternKind
  have bodyIdEq : bodyEntry.identity = bodyId := by
    have observed : identity body = some bodyEntry.identity := by
      simp only [bodyShape, identity]
    exact Option.some.inj (observed.symm.trans bodyIdentity)
  subst bodyId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts
  have bodySelected : decision bodyFirst.1.key universeValue referenceValue = .leftMu := sourceFacts.1
  have sourceValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct entryBefore.native.machine.domains entryPhysical.1.machine.2 _).1
  have bodyKey := SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 sourceValid sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  have diagonalFresh : pair entry.identity entry.identity ∉ bodyFirst.1.key.seen := by
    intro member
    have repeated : decision bodyFirst.1.key universeValue referenceValue =
        .repeated (pair entry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        universeValue, referenceValue, Value.referenceOf, Value.free, member, tagOrder]
    rw [repeated] at bodySelected
    cases bodySelected
  have sourceFresh : pair entry.identity entry.identity ∉ sourceDomain.1.key.seen := by
    intro member
    apply diagonalFresh
    change pair entry.identity entry.identity ∈ bodyFirst.1.key.seen
    rw [bodyKey]
    exact (extend_seen _ _ _ _).mpr (Or.inr member)
  have sourceSameKey : actualDomain.key = sourceDomain.1.key :=
    sameKey.trans (congrArg (fun current => current.key) domainEq)
  have actualFresh : pair entry.identity entry.identity ∉ actualDomain.key.seen := by
    rw [sourceSameKey]
    exact sourceFresh
  have selected : decision request.domain.key request.left request.right = .leftMu := by
    simp [request, decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      universeValue, referenceValue, Value.referenceOf, Value.free, actualFresh, tagOrder]
  have compiled := mu_code request selected
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, total, _queryBeforeFinish, _queryBound,
    queryPrefix, dispatched, _isolated, queryPhysical, _queryReady, _querySafe, _bodyOwner, bodyActual, _resumeEq⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishCount parentHandle request value rest
      beforeFinish (by omega) actual owner
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension dispatched queryPhysical).1
  let allocated := SourceRecursiveIntersectionEnvironment.enter beforeBody.native.machine.domains request.domain.key
    request.left request.right entry.identity entry.identity
  let started : Checked width :=
    {beforeBody with native := advance beforeBody.native {beforeBody.native.machine with domains := allocated.2}}
  let binder := pair entry.identity entry.identity
  let childCode := requestNode allocated.1 body referenceValue
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => .optionalBinder binder product .pure
  let finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun result => .finishNode parentHandle result (resume result)
  let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun product => (next product).bind finishNext
  have leftRead : identity request.left = some entry.identity := rfl
  have one : step (.code (compileNode request)) beforeBody =
      .yielded (.code (childCode.bind next)) started := by
    rw [compiled]
    have receipt := SourceCurrentAllocatedNativeMuSource.enter_prefix request beforeBody
      entry.identity entry.identity leftRead rfl
    simpa only [childCode, requestNode, Code.bind, next, binder, started, allocated,
      request, universeValue, referenceValue, SourceRecursiveIntersectionKernel.body] using receipt
  have bodyEnter : Steps 1 (.code (compileNode request)) beforeBody
      (.code (childCode.bind next)) started := .cons _ _ _ _ _ _ 0 one (.refl _ _)
  have names : (SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst =
      [entry.identity] := by
    simp only [request, universeValue, referenceValue, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder, List.append_nil, List.map_cons, List.map_nil]
  have keyCalculation := SourceRecursiveIntersectionSchedule.entered_key beforeBody.native.machine.domains
    beforePhysical.machine.2 request.domain.key request.left request.right entry.identity entry.identity
  change allocated.1.key = extend request.domain.key
    ((SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst)
    (pair entry.identity entry.identity) at keyCalculation
  have allocatedKey : allocated.1.key =
      extend domain.key [entry.identity] (pair entry.identity entry.identity) := by
    have normalized : allocated.1.key = extend actualDomain.key [entry.identity]
        (pair entry.identity entry.identity) :=
      keyCalculation.trans (congrArg
        (fun bindings => extend request.domain.key bindings (pair entry.identity entry.identity)) names)
    exact normalized.trans (congrArg
      (fun current => extend current [entry.identity] (pair entry.identity entry.identity)) sameKey)
  have liftedBody := bodyEnter.bind _ _ _ _ _ finishNext
  have rootBody := queryPrefix.steps.trans _ _ _ _ _ _ _ _ dispatched.steps
  have intoChild := rootBody.trans _ _ _ _ _ _ _ _ liftedBody
  have childOrigin : Steps (queryUsed + 2) rootControl initialState
      (.code (childCode.bind lifted)) started := by
    simpa only [Control.bind, Code.bind_assoc, Code.bind, finishNext, lifted, Nat.add_assoc] using intoChild
  cases bodyCount with
  | zero =>
      have impossible := steps_zero _ _ _ _ bodyActual
      rw [impossible.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ bodyActual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childCount, optionalCount, product, middle, splitCount, childActual, optionalActual⟩ :=
        steps_bind_inverse remaining (.code childCode) next started beforeFinish value tail
      have keyed : ∃ key, SourceRecursiveIntersectionMemo.requestKey width allocated.1 body referenceValue = some key := by
        rw [bodyShape]
        exact ⟨_, rfl⟩
      obtain ⟨childKey, childKeyEq⟩ := keyed
      have childPast := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
        (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
          entry.identity entry.identity entry.identity
          (extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
            [entry.identity] (pair bodyEntry.identity entry.identity))
          (extend domain.key [entry.identity] (pair entry.identity entry.identity)) body universeValue)
        SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult
        rootRequest start initialPhysical fuel finishCount (queryUsed + 2) childCount
        (.code (.finishNode parentHandle value rest)) beforeFinish (by omega) actual past
        ⟨allocated.1, body, referenceValue⟩ childKey childKeyEq lifted started middle product
        (by omega) childOrigin childActual
      have shape : SourceCurrentAllocatedNativeCoherentOpenBodyResult.ProductShape
          entry.identity entry.identity entry.identity body product :=
        childPast.1.2 allocatedKey rfl rfl
      have childResources := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
        fuel (queryUsed + 2) rootControl (.code childCode) lifted initialState started
        sourceHeap initialPhysical plan fields operationsValid sourceGrowth childOrigin (by omega)
      obtain ⟨_checkedOrigin, childPhysical, _childExtension, childGrowth, _childOperations,
        _childOperationsGrowth, _boundChildPlan, childPlan, _boundChildFields, _childFields⟩ := childResources
      have atEnd := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
        (fuel - (queryUsed + 2)) childCount (.code childCode) (.code (.pure product)) .pure
        started middle childPhysical childPlan childActual (by omega)
      have middleGrowth : Grows sourceHeap middle.native.machine.heap :=
        InternedConstructorTemplates.grows_trans childGrowth atEnd.2.2.1.heap
      have available : Available middle.native.machine.heap product :=
        SourceCurrentNativeOpenRequestResults.node_result childCount
          ⟨allocated.1, body, referenceValue⟩ started middle product childPhysical atEnd.1
      obtain ⟨_reclosed, optionalOne, _optionalDone⟩ :=
        SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          middle atEnd.2.1.machine.1 middleGrowth entry.identity entry.identity product available shape
      exact (optional_reclosed_trace binder product universeValue middle beforeFinish optionalCount value
        optionalOne optionalActual).2.1

end DiagonalOuter

namespace Finish

open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision payload identity tag pair)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)

set_option autoImplicit false

private theorem profile_empty (sourceName : Nat) : Profile sourceName (.empty : Node) := by
  refine ⟨rfl, ?_⟩
  intro atom member
  simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member

private theorem physical_identity_apart_owner
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (entry : Interned NodeKey) (body depth ordinary : Node)
    (ownerAvailable : Available heap (.mu entry body depth ordinary))
    (value : Node) (available : Available heap value)
    (valueId : Nat) (valueIdentity : SourcePreparedSharedRows.reference value = some valueId)
    (different : value ≠ .mu entry body depth ordinary) : valueId ≠ entry.identity := by
  intro same
  have actualIdentity : SourcePreparedSharedRows.reference value = some entry.identity :=
    valueIdentity.trans (congrArg some same)
  have actualRead := SourcePreparedSharedRows.read_identity heap facts value available entry.identity actualIdentity
  have ownerRead := SourcePreparedSharedRows.read_identity heap facts
    (.mu entry body depth ordinary) ownerAvailable entry.identity rfl
  exact different (Option.some.inj (actualRead.symm.trans ownerRead))

private theorem pair_apart_owner (left right owner pattern : Nat)
    (leftApart : left ≠ owner) (rightApart : right ≠ owner) :
    pair left right ≠ pair owner pattern := by
  intro same
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

private theorem mixed_result_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (pattern : Node) (patternId : Nat) (openAlias operand : Node)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId request.domain)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : Profile entry.identity operand)
    (operandHeight : height operand ≤ height pattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) → height operand < height pattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges)
    (innerPast :
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        (.mu entry body depth ordinary)) beforeFinish.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity
        (SourceRecursiveIntersectionDomain.extend
          (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))
          [entry.identity] (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult beforeFinish.native.edges) :
    Profile entry.identity value := by
  have qualified : MixedQualifiedAt (width := width) rootRequest start wholeCount
      entry body depth ordinary request :=
    ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
      operandProfile, operandHeight, strictAlias, ordered⟩
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, _queryBound, queryPrefix, actualDispatch, _isolatedDispatch,
      queryPhysical, queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle request value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.node request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, _queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, _queryInputs, _queryBoundFields, _queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node request .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, bodyAvailable, _bodySourceFacts⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have aliasFree : openAlias.free = [.interned entry.identity] := by
    rcases aliasKind with same | same
    · rw [same, bodyEq]
      rfl
    · rw [same]
      rfl
  have operandAvailable : Available queryBefore.native.machine.heap operand := by
    rcases ordered with ⟨_left, right⟩ | ⟨left, _right⟩
    · simpa only [right] using queryReady.2.2
    · simpa only [left] using queryReady.2.1
  have bodyStart : Trace (queryUsed + 1) (.code (.node rootRequest .pure))
      start
      (.code ((compileNode request).bind
        (fun result => .finishNode handle result (queryResume result)))) beforeBody :=
    queryPrefix.trans actualDispatch
  by_cases rejected : SourceRecursiveIntersectionControl.hasEmpty request.left request.right = true
  · have selected := SourceRecursiveIntersectionControl.empty_first request.domain.key request.left request.right rejected
    have compiled : compileNode request = .pure .empty := by simp only [compileNode, selected]
    rw [compiled] at rawBody
    have pure := pure_trace bodyCount (.empty : Node) value beforeBody beforeFinish rawBody
    rw [← pure.2.1]
    exact profile_empty _
  have noEmpty : SourceRecursiveIntersectionControl.hasEmpty request.left request.right = false := by
    cases observed : SourceRecursiveIntersectionControl.hasEmpty request.left request.right with
    | false => rfl
    | true => exact (rejected observed).elim
  have noReset : SourceRecursiveIntersectionControl.reset request.domain.key request.left request.right = false := by
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · rw [left, right]
      change (openAlias.free.isEmpty && operand.free.isEmpty && !request.domain.key.free.isEmpty) = false
      rw [aliasFree]
      rfl
    · rw [left, right]
      change (operand.free.isEmpty && openAlias.free.isEmpty && !request.domain.key.free.isEmpty) = false
      rw [aliasFree]
      cases operand.free.isEmpty <;> rfl
  by_cases self : SourceRecursiveIntersectionControl.closedSelf request.left request.right = true
  · have selected := SourceRecursiveIntersectionControl.self_first request.domain.key request.left request.right
      noEmpty noReset self
    have compiled : compileNode request = .pure request.left := by simp only [compileNode, selected]
    have same := SourceRecursiveIntersectionControl.self_record queryBefore.native.machine.heap
      queryPhysical.machine.1 request.left request.right queryReady.2.1 queryReady.2.2 self
    have leftProfile : Profile entry.identity request.left := by
      rcases ordered with ⟨_left, right⟩ | ⟨left, _right⟩
      · rw [same, right]
        exact operandProfile
      · rw [left]
        exact operandProfile
    rw [compiled] at rawBody
    have pure := pure_trace bodyCount request.left value beforeBody beforeFinish rawBody
    rw [← pure.2.1]
    exact leftProfile
  have noSelf : SourceRecursiveIntersectionControl.closedSelf request.left request.right = false := by
    cases observed : SourceRecursiveIntersectionControl.closedSelf request.left request.right with
    | false => rfl
    | true => exact (self observed).elim
  by_cases swap : SourceRecursiveIntersectionControl.greater request.left request.right = true
  · have selected := SourceRecursiveIntersectionControl.swap_first request.domain.key request.left request.right
      noEmpty noReset noSelf swap
    let child : NodeRequest Symbol Guard := ⟨request.domain, request.right, request.left⟩
    have childQualified : MixedQualifiedAt (width := width) rootRequest start wholeCount
        entry body depth ordinary child := by
      refine ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
        operandProfile, operandHeight, strictAlias, ?_⟩
      rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
      · exact Or.inr ⟨right, left⟩
      · exact Or.inl ⟨right, left⟩
    have compiled : compileNode request = requestNode child.domain child.left child.right := by
      change compileNode request = requestNode request.domain request.right request.left
      simp only [compileNode, selected]
    have origin : Steps (queryUsed + 1) (.code (.node rootRequest .pure))
        start
        (.code ((requestNode child.domain child.left child.right).bind
          (fun result => .finishNode handle result (queryResume result)))) beforeBody := by
      simpa only [compiled] using bodyStart.steps
    have childActual : Steps bodyCount (.code (requestNode child.domain child.left child.right)) beforeBody
        (.code (.pure value)) beforeFinish := by
      simpa only [compiled] using rawBody
    obtain ⟨childKey, keyed⟩ := warm_qualified_key
      rootRequest start wholeCount entry body depth ordinary bodyCodec child (Or.inr childQualified)
    have law := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
      (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
      (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
      rootRequest start initialPhysical fuel finishUsed (queryUsed + 1) bodyCount (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual past child childKey keyed
      (fun result => .finishNode handle result (queryResume result)) beforeBody beforeFinish value
      (by omega) origin childActual
    exact law.1.2 childQualified
  have noSwap : SourceRecursiveIntersectionControl.greater request.left request.right = false := by
    cases observed : SourceRecursiveIntersectionControl.greater request.left request.right with
    | false => rfl
    | true => exact (swap observed).elim
  have originalEntry := authentic
  obtain ⟨_patternClosed, _patternIdentity, _patternKind, _universeFirst, entryUsed,
      entryBefore, entryNext, entryData⟩ := authentic
  dsimp only at entryData
  obtain ⟨entryBound, entryPrefix, _orderedAllocation, _entryOne, domainEq⟩ := entryData
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) pattern entry.identity patternId
  change request.domain = entered.1 at domainEq
  have entryTotal : entryUsed + (wholeCount - entryUsed) = wholeCount := by omega
  have entryWhole : Trace (entryUsed + (wholeCount - entryUsed)) (.code (.node rootRequest .pure))
      start rest reader := by
    simpa only [entryTotal] using wholeActual
  have entryChecked := SourceCurrentHereditaryNativePhysicalSplit.split entryPrefix.steps entryWhole
  have entryPhysical := SourceCurrentNativeEnterCommonOperand.checked_trace_extension entryChecked.1 initialPhysical
  have enteredKey := SourceRecursiveIntersectionSchedule.entered_key entryBefore.native.machine.domains
    entryPhysical.1.machine.2 IntersectionEmptyDomain.emptyKey
    (.mu entry body depth ordinary) pattern entry.identity patternId
  change entered.1.key = SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey
    ((SourceRecursiveIntersectionEnvironment.bindings (.mu entry body depth ordinary) pattern).map Prod.fst)
    (pair entry.identity patternId) at enteredKey
  have seenOnly : ∀ candidate, candidate ∈ request.domain.key.seen → candidate = pair entry.identity patternId := by
    intro candidate seen
    rw [domainEq, enteredKey] at seen
    rcases (SourceRecursiveIntersectionDomain.extend_seen IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings (.mu entry body depth ordinary) pattern).map Prod.fst)
      (pair entry.identity patternId) candidate).mp seen with same | old
    · exact same
    · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at old
  cases operand with
  | empty =>
      have rejected : SourceRecursiveIntersectionControl.hasEmpty request.left request.right = true := by
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩ <;>
          simp [SourceRecursiveIntersectionControl.hasEmpty, left, right, Value.referenceOf]
      rw [rejected] at noEmpty
      cases noEmpty
  | reference name =>
      have closed := operandProfile.1
      cases closed
  | union own members level free =>
      exact SourceCurrentNativeWarmMixedFinish.Union.mixed_union_profile_at_actual_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        rootRequest start initialPhysical sourceGrowth operationsValid fuel wholeCount finishUsed handle
        request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
        inputs fields ⟨own, members, level, free, by
          rcases ordered with ⟨_left, right⟩ | ⟨left, _right⟩
          · exact Or.inr right
          · exact Or.inl left⟩ qualified past
  | node own rows level free =>
      have freeEq : free = [] := operandProfile.1
      subst free
      rcases aliasKind with bodyAlias | referenceAlias
      · subst openAlias
        have ownerAvailable : Available queryBefore.native.machine.heap (.mu entry body depth ordinary) :=
          queryPhysical.machine.1.cached.nodes key _ (queryGrowth.nodeRecords key _ stored)
        have actualBody : Available queryBefore.native.machine.heap
            (.node bodyEntry (canonicalEdges (_arrow :: _sourceRows)) 0 [.interned entry.identity]) :=
          bodyEq ▸ bodyAvailable
        have bodyApart := physical_identity_apart_owner queryBefore.native.machine.heap queryPhysical.machine.1
          entry body depth ordinary ownerAvailable
          (.node bodyEntry (canonicalEdges (_arrow :: _sourceRows)) 0 [.interned entry.identity]) actualBody
          bodyEntry.identity rfl (by intro impossible; cases impossible)
        have operandApart := physical_identity_apart_owner queryBefore.native.machine.heap queryPhysical.machine.1
          entry body depth ordinary ownerAvailable (.node own rows level []) operandAvailable own.identity rfl
          (by intro impossible; cases impossible)
        have directFresh : pair bodyEntry.identity own.identity ∉ request.domain.key.seen := by
          intro seen
          exact pair_apart_owner bodyEntry.identity own.identity entry.identity patternId bodyApart operandApart
            (seenOnly _ seen)
        have reverseFresh : pair own.identity bodyEntry.identity ∉ request.domain.key.seen := by
          intro seen
          exact pair_apart_owner own.identity bodyEntry.identity entry.identity patternId operandApart bodyApart
            (seenOnly _ seen)
        have selected : decision request.domain.key request.left request.right = .ordinary := by
          unfold decision
          simp only [noEmpty, noReset, noSelf, noSwap, Bool.false_eq_true, ite_false]
          rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
          · simp only [left, right, bodyEq, identity, directFresh, payload, ite_false]
          · simp only [left, right, bodyEq, identity, reverseFresh, payload, ite_false]
        exact SourceCurrentNativeWarmMixedFinish.Ordinary.mixed_ordinary_profile_at_actual_node_finish
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          rootRequest start initialPhysical sourceGrowth operationsValid fuel wholeCount finishUsed handle
          request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
          inputs fields selected qualified past
      · subst openAlias
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · exact SourceCurrentNativeWarmMixedFinish.ReferenceNode.mixed_reference_node_profile_at_actual_node_finish
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            rootRequest start initialPhysical sourceGrowth operationsValid fuel wholeCount finishUsed handle
            request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
            inputs fields true own rows level ⟨left, right⟩ qualified past
        · exact SourceCurrentNativeWarmMixedFinish.ReferenceNode.mixed_reference_node_profile_at_actual_node_finish
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            rootRequest start initialPhysical sourceGrowth operationsValid fuel wholeCount finishUsed handle
            request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
            inputs fields false own rows level ⟨left, right⟩ qualified past
  | mu own ownBody ownDepth ownOrdinary =>
      have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth own ownBody ownDepth ownOrdinary
        operandAvailable operandProfile.1 operandProfile.2
      have universeProfile : Profile entry.identity (.mu entry body depth ordinary) := by
        rw [← same]
        exact operandProfile
      rcases aliasKind with bodyAlias | referenceAlias
      · subst openAlias
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · have requestEq : request = ⟨request.domain, body, .mu entry body depth ordinary⟩ := by
            change (⟨request.domain, request.left, request.right⟩ : NodeRequest Symbol Guard) = _
            rw [left, right, same]
          have held : beforeFinish.native.nodes.cells handle =
              some ⟨⟨request.domain, body, .mu entry body depth ordinary⟩, .evaluating⟩ :=
            requestEq ▸ owner
          have valueEq := SourceCurrentNativeWarmMixedFinish.BodyFirstOuter.body_first_outer_finish_of_past_body_first_key_law
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            bodyId bodyIdentity rootRequest start initialPhysical operationsValid sourceGrowth
            fuel wholeCount finishUsed pattern patternId request.domain request.domain originalEntry rfl
            handle value parentNext beforeFinish rest reader wholeBound wholeActual (by omega) actual held
            inputs fields innerPast.1
          rw [valueEq]
          exact universeProfile
        · have wrong : SourceRecursiveIntersectionControl.greater request.left request.right = true := by
            rw [left, right, same, bodyEq]
            rfl
          rw [wrong] at noSwap
          cases noSwap
      · subst openAlias
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · have wrong : SourceRecursiveIntersectionControl.greater request.left request.right = true := by
            rw [left, right, same]
            rfl
          rw [wrong] at noSwap
          cases noSwap
        · have requestEq : request =
              ⟨request.domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩ := by
            change (⟨request.domain, request.left, request.right⟩ : NodeRequest Symbol Guard) = _
            rw [left, right, same]
          have held : beforeFinish.native.nodes.cells handle =
              some ⟨⟨request.domain, .mu entry body depth ordinary,
                .reference (.interned entry.identity)⟩, .evaluating⟩ :=
            requestEq ▸ owner
          have valueEq := SourceCurrentNativeWarmMixedFinish.DiagonalOuter.diagonal_outer_finish_of_past_coherent_laws
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            bodyId bodyIdentity rootRequest start initialPhysical operationsValid sourceGrowth
            fuel wholeCount finishUsed pattern patternId request.domain request.domain originalEntry rfl
            handle value parentNext beforeFinish rest reader wholeBound wholeActual (by omega) actual held
            inputs fields innerPast.2.2
          rw [valueEq]
          exact universeProfile

end Finish

theorem mixed_result_at_actual_warm_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
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
    (newRoot : NodeRequest Symbol Guard) (newFuel newCount : Nat)
    (newControl : Control (Value Symbol Guard)) (warmReader : Checked width)
    (newBound : newCount ≤ newFuel)
    (newInputs : InputsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newFields : FieldsThrough newFuel (.code (.node newRoot .pure)) oldSnapshot)
    (newActual : Trace newCount (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader)
    (finishUsed handle : Nat) (request : NodeRequest Symbol Guard) (value : Node)
    (parentNext : Code Symbol Guard Node) (beforeFinish : Checked width)
    (finishBound : finishUsed < newCount)
    (actual : Trace finishUsed (.code (.node newRoot .pure)) oldSnapshot
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (pattern : Node) (patternId : Nat) (openAlias operand : Node)
    (authentic : AuthenticEntryAt (width := width) newRoot oldSnapshot newCount
      entry body depth ordinary pattern patternId request.domain)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : Profile entry.identity operand)
    (operandHeight : height operand ≤ height pattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) → height operand < height pattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))
    (past :
      Returned (NodeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) newRoot oldSnapshot newCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value
 := by
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have innerPast := SourceCurrentNativeWarmAuxiliaryPrefixes.auxiliary_payloads_at_every_actual_warm_prefix
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth operations operationsValid
    oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel newCount newControl warmReader newBound newInputs newFields newActual
    finishUsed (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual
    pattern patternId request.domain authentic
  dsimp only at innerPast
  exact Finish.mixed_result_at_actual_node_finish
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity newRoot oldSnapshot oldOperations.2.1 oldOperations.2.2.2.1
    oldOperations.2.2.2.2.1 newFuel newCount finishUsed handle request value newControl warmReader beforeFinish
    parentNext newBound newActual finishBound actual owner newInputs newFields
    pattern patternId openAlias operand authentic aliasKind operandProfile operandHeight strictAlias ordered past innerPast

end MicroCFTA.SourceCurrentNativeWarmMixedFinish

namespace MicroCFTA.SourceCurrentNativeWarmMixedFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
open SourceCurrentNativeWarmCMDefinitions (NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Mixed finish with genuine past inner laws]
This export keeps the exact actual finish and all before-finish laws.
The four inner laws are local induction inputs at that same state.
The source-facing worker must derive them from its actual history.
This component supplies no source seed or future cache meaning.
-/
theorem mixed_result_at_actual_warm_node_finish_of_past_inner_laws
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value parentNext)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (pattern : Node) (patternId : Nat) (openAlias operand : Node)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId request.domain)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : Profile entry.identity operand)
    (operandHeight : height operand ≤ height pattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) → height operand < height pattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges)
    (innerPast :
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        (.mu entry body depth ordinary)) beforeFinish.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity
        (SourceRecursiveIntersectionDomain.extend
          (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))
          [entry.identity] (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        (SourceRecursiveIntersectionDomain.extend request.domain.key [entry.identity]
          (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))
        body (.mu entry body depth ordinary)) beforeFinish.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult beforeFinish.native.edges) :
    Profile entry.identity value := by
  exact Finish.mixed_result_at_actual_node_finish (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
    fuel wholeCount finishUsed handle request value rest reader beforeFinish parentNext
    wholeBound wholeActual finishBound actual owner inputs fields
    pattern patternId openAlias operand authentic aliasKind operandProfile operandHeight strictAlias
    ordered past innerPast

end MicroCFTA.SourceCurrentNativeWarmMixedFinish
