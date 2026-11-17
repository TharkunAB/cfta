import MicroCFTA.SourceCurrentAllocatedNativeGeneralCNodeFinish
import MicroCFTA.SourceCurrentNativeWarmCMDefinitions

namespace MicroCFTA.SourceCurrentNativeWarmCNodeFinish
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceRecursiveIntersectionControl (decision payload identity tag pair)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
  (ordinary_code make_node_profile all₂_row_profiles)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Node" => Value Symbol Guard
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/- Note [Closed results on one actual warm history]
The full warm trace fixes every later mixed qualifier. Each observed finish
retains its actual root prefix. The selected closed Mu case appends its
literal enter event to that prefix before it uses the mixed past law.
Both child readers use the same before-finish native tables and suffix.
No empty-table reset or unrelated entry witness is used.
-/

private theorem profile_empty (sourceName : Nat) : Profile sourceName (.empty : Value Symbol Guard) := by
  refine ⟨rfl, ?_⟩
  intro atom member
  simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member

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

private theorem qualified_key
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

private theorem closed_identity (value : Node) (closed : value.free = []) (nonempty : value ≠ .empty) :
    ∃ name, identity value = some name := by
  cases value with
  | empty => exact (nonempty rfl).elim
  | reference name => cases closed
  | node own rows depth free => exact ⟨own.identity, rfl⟩
  | union own members depth free => exact ⟨own.identity, rfl⟩
  | mu own body depth ordinary => exact ⟨own.identity, rfl⟩

private theorem pattern_body (pattern : Node) (kind : tag pattern = 1 ∨ tag pattern = 3) :
    SourceRecursiveIntersectionKernel.body pattern = pattern := by
  cases pattern <;> simp_all [tag, SourceRecursiveIntersectionKernel.body]

private theorem closed_ordinary_domain (sourceName : Nat) (request : NodeRequest Symbol Guard)
    (qualified : ClosedQualified sourceName request)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary) :
    request.domain = IntersectionEmptyDomain.emptyDomain := by
  rcases qualified.2.2 with empty | active
  · exact empty
  · have restart : SourceRecursiveIntersectionControl.reset request.domain.key request.left request.right = true := by
      simp only [SourceRecursiveIntersectionControl.reset, qualified.1.1, qualified.2.1.1,
        List.isEmpty_nil, active, Bool.not_false, Bool.and_self]
    cases emptyTest : SourceRecursiveIntersectionControl.hasEmpty request.left request.right with
    | false =>
      have first := SourceRecursiveIntersectionControl.reset_first request.domain.key request.left request.right
        emptyTest restart
      rw [first] at selected
      cases selected
    | true =>
      have first := SourceRecursiveIntersectionControl.empty_first request.domain.key request.left request.right emptyTest
      rw [first] at selected
      cases selected

private theorem original_child_profile
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (sourceName : Nat)
    (parent : Value Symbol Guard) (available : Available heap parent) (profile : Profile sourceName parent)
    (row : EdgeValue Symbol Guard) (rowMember : row ∈ nodeEdges parent)
    (child : Value Symbol Guard) (childMember : child ∈ row.children) : Profile sourceName child := by
  cases parent with
  | node entry rows depth free =>
    have member : row ∈ rows := rowMember
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
      heap facts sourceName entry rows depth free available profile.1 profile.2 row member child childMember
    exact ⟨inherited.2.1, inherited.2.2⟩
  | empty | reference | union | mu => simp only [nodeEdges, List.not_mem_nil] at rowMember


private theorem closed_ordinary_profile_at_actual_warm_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (_accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (_built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (_stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount finishUsed handle : Nat)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (_wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
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
    (qualified : ClosedQualified entry.identity request)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value
 := by
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
  have domainEmpty := closed_ordinary_domain entry.identity request qualified selected
  have originalPairsQualified : ∀ pair ∈ pairs (nodeEdges request.left) (nodeEdges request.right),
      ∀ children ∈ pair.1.children.zip pair.2.children,
        Qualified (width := width) rootRequest start wholeCount entry body depth ordinary
          ⟨request.domain, children.1, children.2⟩ := by
    intro pair matched children included
    have rows := (pairs_member (nodeEdges request.left) (nodeEdges request.right) pair).mp matched
    have inside := List.of_mem_zip included
    have first := original_child_profile queryBefore.native.machine.heap queryPhysical.machine.1 entry.identity
      request.left queryReady.2.1 qualified.1 pair.1 rows.1 children.1 inside.1
    have second := original_child_profile queryBefore.native.machine.heap queryPhysical.machine.1 entry.identity
      request.right queryReady.2.2 qualified.2.1 pair.2 rows.2.1 children.2 inside.2
    exact Or.inl ⟨first, second, Or.inl domainEmpty⟩
  have compiled := ordinary_code request selected
  have rowsTrace : Trace bodyCount
      (.code (compileRows request.domain (nodeEdges request.left) (nodeEdges request.right))) beforeBody
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
    request.domain (nodeEdges request.left) (nodeEdges request.right) beforeBody beforeFinish
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


theorem closed_result_at_actual_warm_node_finish
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
    (_wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
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
    (qualified : ClosedQualified entry.identity request)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value
 := by
  rcases request with ⟨domain, left, right⟩
  let parent : NodeRequest Symbol Guard := ⟨domain, left, right⟩
  change ClosedQualified entry.identity parent at qualified
  change beforeFinish.native.nodes.cells handle = some ⟨parent, .evaluating⟩ at owner
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyEq]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have bodyNotReference : body ≠ .reference (.interned entry.identity) := by
    intro same
    rw [bodyEq] at same
    cases same
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, _queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, bodyOwner, rawBody, queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle parent value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.node parent .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node parent .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  have bodyPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension actualDispatch queryPhysical).1
  let finishNext : Node → Code Symbol Guard Node :=
    fun result => .finishNode handle result (queryResume result)
  have bodyStart : Trace (queryUsed + 1) (.code (.node rootRequest .pure))
      start
      (.code ((compileNode parent).bind finishNext)) beforeBody := by
    simpa only [finishNext] using queryPrefix.trans actualDispatch
  have atParent : Trace (queryUsed + 1 + bodyCount) (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value (queryResume value))) beforeFinish := by
    simpa only [total, queryRest] using actual
  have childResult (child : NodeRequest Symbol Guard) (used childCount : Nat)
      (next : Node → Code Symbol Guard Node) (first last : Checked width) (childValue : Node)
      (within : used + childCount ≤ finishUsed)
      (origin : Steps used (.code (.node rootRequest .pure))
        start
        (.code ((requestNode child.domain child.left child.right).bind next)) first)
      (childActual : Steps childCount (.code (requestNode child.domain child.left child.right)) first
        (.code (.pure childValue)) last)
      (childQualified : Qualified (width := width) rootRequest start wholeCount
        entry body depth ordinary child) : Profile entry.identity childValue := by
    obtain ⟨childKey, keyed⟩ := qualified_key rootRequest start wholeCount
      entry body depth ordinary bodyCodec child childQualified
    have law := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
      (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
      (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
      rootRequest start initialPhysical fuel finishUsed used childCount
      (.code (.finishNode handle value parentNext)) beforeFinish (by omega) actual past
      child childKey keyed next first last childValue within origin childActual
    rcases childQualified with closed | mixed
    · exact law.1.1 closed
    · exact law.1.2 mixed
  have forwarded (child : NodeRequest Symbol Guard) (childQualified : ClosedQualified entry.identity child)
      (compiled : compileNode parent = requestNode child.domain child.left child.right) : Profile entry.identity value := by
    have origin : Steps (queryUsed + 1) (.code (.node rootRequest .pure))
        start
        (.code ((requestNode child.domain child.left child.right).bind finishNext)) beforeBody := by
      simpa only [compiled] using bodyStart.steps
    have called : Steps bodyCount (.code (requestNode child.domain child.left child.right)) beforeBody
        (.code (.pure value)) beforeFinish := by simpa only [compiled] using rawBody
    exact childResult child (queryUsed + 1) bodyCount finishNext beforeBody beforeFinish value
      (by omega) origin called (Or.inl childQualified)
  have leftProfile : Profile entry.identity left := qualified.1
  have rightProfile : Profile entry.identity right := qualified.2.1
  have leftClosed := leftProfile.1
  have rightClosed := rightProfile.1
  have leftAvailable : Available queryBefore.native.machine.heap left := queryReady.2.1
  have rightAvailable : Available queryBefore.native.machine.heap right := queryReady.2.2
  by_cases empty : SourceRecursiveIntersectionControl.hasEmpty left right = true
  · have selected := SourceRecursiveIntersectionControl.empty_first domain.key left right empty
    have compiled : compileNode parent = .pure .empty := by simp only [compileNode, parent, selected]
    rw [compiled] at rawBody
    have pure := pure_trace bodyCount (.empty : Node) value beforeBody beforeFinish rawBody
    rw [← pure.2.1]
    exact profile_empty _
  have noEmpty : SourceRecursiveIntersectionControl.hasEmpty left right = false := by
    cases observed : SourceRecursiveIntersectionControl.hasEmpty left right with
    | false => rfl
    | true => exact (empty observed).elim
  by_cases restart : SourceRecursiveIntersectionControl.reset domain.key left right = true
  · have selected := SourceRecursiveIntersectionControl.reset_first domain.key left right noEmpty restart
    apply forwarded ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
      ⟨leftProfile, rightProfile, Or.inl rfl⟩
    simp only [compileNode, parent, selected]
  have noReset : SourceRecursiveIntersectionControl.reset domain.key left right = false := by
    cases observed : SourceRecursiveIntersectionControl.reset domain.key left right with
    | false => rfl
    | true => exact (restart observed).elim
  by_cases self : SourceRecursiveIntersectionControl.closedSelf left right = true
  · have selected := SourceRecursiveIntersectionControl.self_first domain.key left right noEmpty noReset self
    have compiled : compileNode parent = .pure left := by simp only [compileNode, parent, selected]
    rw [compiled] at rawBody
    have pure := pure_trace bodyCount left value beforeBody beforeFinish rawBody
    rw [← pure.2.1]
    exact leftProfile
  have noSelf : SourceRecursiveIntersectionControl.closedSelf left right = false := by
    cases observed : SourceRecursiveIntersectionControl.closedSelf left right with
    | false => rfl
    | true => exact (self observed).elim
  by_cases swap : SourceRecursiveIntersectionControl.greater left right = true
  · have selected := SourceRecursiveIntersectionControl.swap_first domain.key left right noEmpty noReset noSelf swap
    apply forwarded ⟨domain, right, left⟩ ⟨rightProfile, leftProfile, qualified.2.2⟩
    simp only [compileNode, parent, selected]
  have noSwap : SourceRecursiveIntersectionControl.greater left right = false := by
    cases observed : SourceRecursiveIntersectionControl.greater left right with
    | false => rfl
    | true => exact (swap observed).elim
  have domainEmpty : domain = IntersectionEmptyDomain.emptyDomain := by
    rcases qualified.2.2 with same | active
    · exact same
    · change domain.key.free.isEmpty = false at active
      have reset : SourceRecursiveIntersectionControl.reset domain.key left right = true := by
        simp only [SourceRecursiveIntersectionControl.reset, leftClosed, rightClosed,
          List.isEmpty_nil, active, Bool.not_false, Bool.and_self]
      rw [reset] at noReset
      cases noReset
  subst domain
  have leftNonempty : left ≠ .empty := by
    intro same
    rw [same] at noEmpty
    simp [SourceRecursiveIntersectionControl.hasEmpty, Value.referenceOf] at noEmpty
  have rightNonempty : right ≠ .empty := by
    intro same
    rw [same] at noEmpty
    simp [SourceRecursiveIntersectionControl.hasEmpty, Value.referenceOf] at noEmpty
  obtain ⟨leftId, leftIdentity⟩ := closed_identity left leftClosed leftNonempty
  obtain ⟨rightId, rightIdentity⟩ := closed_identity right rightClosed rightNonempty
  have selectedPayload : decision IntersectionEmptyDomain.emptyDomain.key left right = payload left right := by
    change (if SourceRecursiveIntersectionControl.hasEmpty left right then .empty
      else if SourceRecursiveIntersectionControl.reset IntersectionEmptyDomain.emptyDomain.key left right then .reset
      else if SourceRecursiveIntersectionControl.closedSelf left right then .self
      else if SourceRecursiveIntersectionControl.greater left right then .swap
      else match identity left, identity right with
        | some first, some second =>
            if pair first second ∈ ([] : List (Nat × Nat)) then .repeated (pair first second)
            else payload left right
        | _, _ => .unsupported) = payload left right
    simp only [noEmpty, noReset, noSelf, noSwap, Bool.false_eq_true, ite_false,
      leftIdentity, rightIdentity, List.not_mem_nil]
  have unionRun (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference)
      (other : Node) (side : Bool)
      (unionProfile : Profile entry.identity (.union unionEntry members level free))
      (otherProfile : Profile entry.identity other)
      (sameParent : parent = ⟨IntersectionEmptyDomain.emptyDomain,
        if side then .union unionEntry members level free else other,
        if side then other else .union unionEntry members level free⟩)
      (selected : decision IntersectionEmptyDomain.emptyDomain.key
        (if side then .union unionEntry members level free else other)
        (if side then other else .union unionEntry members level free) =
        (if side then .leftUnion else .rightUnion)) : Profile entry.identity value := by
    let literal : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
      if side then .union unionEntry members level free else other,
      if side then other else .union unionEntry members level free⟩
    have pref := queryPrefix
    have dispatched := isolatedDispatch
    have completed := rawBody
    have plan := queryInputs
    have fieldPlan := queryFields
    rw [sameParent] at pref dispatched completed plan fieldPlan
    have observed := SourceCurrentAllocatedNativeClosedUnionProfile.closed_union_body_profile_of_fuel_induction
      sourceHeap entry.identity unionEntry members level free other side unionProfile otherProfile
      queryBefore beforeBody beforeFinish (fuel - queryUsed) bodyCount value
      (fun result => .finishNode handle result (.pure result)) queryPhysical queryGrowth queryOperations
      plan fieldPlan selected dispatched (by omega) completed (by
        intro child used childFuel childCount _positive _childSmaller _room _countBound span
          emptyDomain firstProfile secondProfile _height next first last childValue origin
          _physical _growth _operations _inputs _fields _firstAvailable _secondAvailable childActual
        let lifted : Node → Code Symbol Guard Node := fun result => (next result).bind queryResume
        have appended := origin.bind _ _ _ _ _ queryResume
        change Steps used (.code (.node literal queryResume)) queryBefore
          (.code (((requestNode child.domain child.left child.right).bind next).bind queryResume)) first at appended
        have tail : Steps used (.code (.node literal queryResume)) queryBefore
            (.code ((requestNode child.domain child.left child.right).bind lifted)) first := by
          simpa only [Code.bind_assoc, lifted] using appended
        have outer : Steps (queryUsed + used) (.code (.node rootRequest .pure))
            start
            (.code ((requestNode child.domain child.left child.right).bind lifted)) first :=
          pref.steps.trans _ _ _ _ _ _ _ _ tail
        exact childResult child (queryUsed + used) childCount lifted first last childValue (by omega)
          outer childActual (Or.inl ⟨firstProfile, secondProfile, Or.inl emptyDomain⟩))
    exact observed.1
  have muRun (pattern : Node) (patternId : Nat) (patternProfile : Profile entry.identity pattern)
      (patternIdentity : identity pattern = some patternId) (patternKind : tag pattern = 1 ∨ tag pattern = 3)
      (side : Bool) (universeClosed : (Value.mu entry body depth ordinary).free = [])
      (sameParent : parent = ⟨IntersectionEmptyDomain.emptyDomain,
        if side then .mu entry body depth ordinary else pattern,
        if side then pattern else .mu entry body depth ordinary⟩)
      (selected : decision IntersectionEmptyDomain.emptyDomain.key
        (if side then .mu entry body depth ordinary else pattern)
        (if side then pattern else .mu entry body depth ordinary) =
        (if side then .leftMu else .rightMu)) : Profile entry.identity value := by
    let universeValue : Node := .mu entry body depth ordinary
    let literal : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,
      if side then universeValue else pattern, if side then pattern else universeValue⟩
    let childLeft : Node := if side then body else pattern
    let childRight : Node := if side then pattern else body
    let firstId := if side then entry.identity else patternId
    let secondId := if side then patternId else entry.identity
    let entered := SourceRecursiveIntersectionEnvironment.enter beforeBody.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    let started : Checked width :=
      {beforeBody with native := advance beforeBody.native {beforeBody.native.machine with domains := entered.2}}
    let binder := pair entry.identity patternId
    let enterNext := fun domain => (requestNode domain childLeft childRight).bind
      (fun result => .optionalBinder binder result .pure)
    have pref := queryOrigin
    have dispatched := isolatedDispatch
    have completed := rawBody
    have plan := queryInputs
    have fieldPlan := queryFields
    have held := bodyOwner
    have compiledPrefix := bodyStart
    rw [sameParent] at pref dispatched completed plan fieldPlan held compiledPrefix
    have bodyPattern := pattern_body pattern patternKind
    have leftIdentity : identity literal.left = some firstId := by
      cases side with
      | false => exact patternIdentity
      | true => rfl
    have rightIdentity : identity literal.right = some secondId := by
      cases side with
      | false => rfl
      | true => exact patternIdentity
    have leftBody : SourceRecursiveIntersectionKernel.body literal.left = childLeft := by
      cases side with
      | false => exact bodyPattern
      | true => rfl
    have rightBody : SourceRecursiveIntersectionKernel.body literal.right = childRight := by
      cases side with
      | false => rfl
      | true => exact bodyPattern
    have paired : pair firstId secondId = binder := by
      cases side with
      | false =>
          change pair patternId entry.identity = pair entry.identity patternId
          simp only [pair, Nat.min_comm, Nat.max_comm]
      | true => rfl
    have selectedCompile : compileNode literal = compileMu literal.domain literal.left literal.right := by
      cases side with
      | false =>
          change decision literal.domain.key literal.left literal.right = .rightMu at selected
          simp only [compileNode, selected]
      | true =>
          change decision literal.domain.key literal.left literal.right = .leftMu at selected
          simp only [compileNode, selected]
    have compiled : compileNode literal = .enter IntersectionEmptyDomain.emptyDomain
        literal.left literal.right firstId secondId enterNext := by
      rw [selectedCompile]
      change compileMu IntersectionEmptyDomain.emptyDomain literal.left literal.right =
        .enter IntersectionEmptyDomain.emptyDomain literal.left literal.right firstId secondId enterNext
      simp only [compileMu, leftIdentity, rightIdentity, leftBody, rightBody, paired,
        enterNext, requestNode, Code.bind]
    change Trace (queryUsed + 1) (.code (.node rootRequest .pure))
      start
      (.code ((compileNode literal).bind finishNext)) beforeBody at compiledPrefix
    have eventPrefix : Trace (queryUsed + 1) (.code (.node rootRequest .pure))
        start
        (.code (.enter IntersectionEmptyDomain.emptyDomain literal.left literal.right firstId secondId
          (fun domain => (enterNext domain).bind finishNext))) beforeBody := by
      simpa only [compiled, Code.bind] using compiledPrefix
    have observed := SourceCurrentAllocatedNativeClosedUniverseMuProfile.closed_universe_mu_profile_trace_result
      sourceHeap key entry body depth ordinary stored universeClosed pattern patternProfile
      patternId patternIdentity patternKind side queryBefore beforeBody beforeFinish (fuel - queryUsed)
      bodyCount value (fun result => .finishNode handle result (.pure result))
      queryPhysical queryGrowth queryOperations selected plan fieldPlan dispatched (by omega) completed (by
        intro childFuel childCount _childSmaller _countBound _room _parentRoom next childValue middle
          origin event _physical _growth _operations _inputs _fields _domain _leftAvailable _rightAvailable
          _universeClosed _patternProfile _height childActual
        let child : NodeRequest Symbol Guard := ⟨entered.1, childLeft, childRight⟩
        have span := SourceCurrentAllocatedNativeNodeChildBeforeFinish.completed_node_child_span_before_parent_finish
          (.code (.node rootRequest .pure)) queryResume literal child handle
          start queryBefore beforeBody beforeFinish started middle
          (fuel - queryUsed) bodyCount queryUsed 2 childCount value childValue next
          bodyPhysical.shape held (by omega) atParent pref dispatched completed (by omega) origin childActual
        have rootSpan := span.2.1
        have allocation := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
          entry body depth ordinary pattern patternProfile.1 patternId patternIdentity patternKind side enterNext
          0 beforeBody started (.code (enterNext entered.1)) bodyPhysical event
        have eventBound : Trace 1
            (.code (.enter IntersectionEmptyDomain.emptyDomain literal.left literal.right firstId secondId
              (fun domain => (enterNext domain).bind finishNext))) beforeBody
            (.code ((enterNext entered.1).bind finishNext)) started := by
          simpa only [Control.bind, Code.bind] using event.bind finishNext
        have authenticated : AuthenticEntryAt (width := width) rootRequest start wholeCount
            entry body depth ordinary pattern patternId entered.1 := by
          refine ⟨patternProfile.1, patternIdentity, patternKind, side, queryUsed + 1, beforeBody,
            (fun domain => (enterNext domain).bind finishNext), ?_⟩
          dsimp only
          exact ⟨by omega, eventPrefix, allocation.1, eventBound, rfl⟩
        have qualifiedChild : Qualified (width := width) rootRequest start wholeCount
            entry body depth ordinary child := by
          refine Or.inr ⟨pattern, patternId, body, pattern, authenticated, Or.inl rfl,
            patternProfile, Nat.le_refl _, ?_, ?_⟩
          · intro same
            exact (bodyNotReference same).elim
          · cases side with
            | false => exact Or.inr ⟨rfl, rfl⟩
            | true => exact Or.inl ⟨rfl, rfl⟩
        exact childResult child (queryUsed + 2) childCount
          (fun result => (next result).bind queryResume) started middle childValue (by omega)
          span.2.2.2.2.2.1.steps childActual qualifiedChild)
    exact observed.1
  cases left <;> cases right
  all_goals try solve | cases leftClosed
  all_goals try solve | cases rightClosed
  all_goals try solve | cases leftIdentity
  all_goals try solve | cases rightIdentity
  case node.node first firstRows firstLevel firstFree second secondRows secondLevel secondFree =>
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.node first firstRows firstLevel firstFree) (.node second secondRows secondLevel secondFree) = .ordinary := by
      simpa only [payload] using selectedPayload
    exact closed_ordinary_profile_at_actual_warm_node_finish
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest start initialPhysical sourceGrowth operationsValid fuel wholeCount finishUsed handle
      parent value rest reader beforeFinish parentNext wholeBound _wholeActual finishBound actual owner
      inputs fields selected qualified past
  case node.union own rows level free other members otherLevel otherFree =>
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.node own rows level free) (.union other members otherLevel otherFree) = .rightUnion := by
      simpa only [payload] using selectedPayload
    exact unionRun other members otherLevel otherFree (.node own rows level free) false
      rightProfile leftProfile rfl selected
  case union.node own members level free other rows otherLevel otherFree =>
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.union own members level free) (.node other rows otherLevel otherFree) = .leftUnion := by
      simpa only [payload] using selectedPayload
    exact unionRun own members level free (.node other rows otherLevel otherFree) true
      leftProfile rightProfile rfl selected
  case union.union own members level free other otherMembers otherLevel otherFree =>
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.union own members level free) (.union other otherMembers otherLevel otherFree) = .leftUnion := by
      simpa only [payload] using selectedPayload
    exact unionRun own members level free (.union other otherMembers otherLevel otherFree) true
      leftProfile rightProfile rfl selected
  case mu.node own ownBody ownDepth ownOrdinary other rows level free =>
    have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth own ownBody ownDepth ownOrdinary
      leftAvailable leftClosed leftProfile.2
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.mu own ownBody ownDepth ownOrdinary) (.node other rows level free) = .leftMu := by
      simpa only [payload] using selectedPayload
    rw [same] at selected
    exact muRun (.node other rows level free) other.identity rightProfile rfl (Or.inl rfl) true
      (by rw [← same]; exact leftClosed) (by simp [parent, same]) selected
  case mu.union own ownBody ownDepth ownOrdinary other members level free =>
    have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth own ownBody ownDepth ownOrdinary
      leftAvailable leftClosed leftProfile.2
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.mu own ownBody ownDepth ownOrdinary) (.union other members level free) = .leftMu := by
      simpa only [payload] using selectedPayload
    rw [same] at selected
    exact muRun (.union other members level free) other.identity rightProfile rfl (Or.inr rfl) true
      (by rw [← same]; exact leftClosed) (by simp [parent, same]) selected
  case node.mu own rows level free other otherBody otherDepth otherOrdinary =>
    have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth other otherBody otherDepth otherOrdinary
      rightAvailable rightClosed rightProfile.2
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.node own rows level free) (.mu other otherBody otherDepth otherOrdinary) = .rightMu := by
      simpa only [payload] using selectedPayload
    rw [same] at selected
    exact muRun (.node own rows level free) own.identity leftProfile rfl (Or.inl rfl) false
      (by rw [← same]; exact rightClosed) (by simp [parent, same]) selected
  case union.mu own members level free other otherBody otherDepth otherOrdinary =>
    have same := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth other otherBody otherDepth otherOrdinary
      rightAvailable rightClosed rightProfile.2
    have selected : decision IntersectionEmptyDomain.emptyDomain.key
        (.union own members level free) (.mu other otherBody otherDepth otherOrdinary) = .rightMu := by
      simpa only [payload] using selectedPayload
    rw [same] at selected
    exact muRun (.union own members level free) own.identity leftProfile rfl (Or.inr rfl) false
      (by rw [← same]; exact rightClosed) (by simp [parent, same]) selected
  case mu.mu own ownBody ownDepth ownOrdinary other otherBody otherDepth otherOrdinary =>
    have firstSame := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth own ownBody ownDepth ownOrdinary
      leftAvailable leftClosed leftProfile.2
    have secondSame := SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      queryBefore.native.machine.heap queryPhysical.machine.1 queryGrowth other otherBody otherDepth otherOrdinary
      rightAvailable rightClosed rightProfile.2
    have universeClosed : (Value.mu entry body depth ordinary).free = [] := by
      rw [← firstSame]
      exact leftClosed
    have reuse : SourceRecursiveIntersectionControl.closedSelf
        (.mu entry body depth ordinary) (.mu entry body depth ordinary) = true := by
      simp only [SourceRecursiveIntersectionControl.closedSelf, beq_self_eq_true,
        universeClosed, List.isEmpty_nil, Bool.and_self]
    rw [firstSame, secondSame, reuse] at noSelf
    cases noSelf


end MicroCFTA.SourceCurrentNativeWarmCNodeFinish
