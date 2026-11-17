import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMEdgeFinish
import MicroCFTA.SourceCurrentNativeWarmCMDefinitions

namespace MicroCFTA.SourceCurrentNativeWarmEdgeFinish
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Edge results on one actual warm history]
The actual edge finish and each child stay on the same warm root trace.
The full history remains fixed in every child qualification.
The past node law applies to the same child's retained returned cell.
All original zipped child conditions remain in the result predicate.
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

theorem qualified_edge_result_at_actual_warm_edge_finish
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
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard)
    (rest : Control (Value Symbol Guard)) (reader beforeFinish : Checked width)
    (parentNext : Code Symbol Guard (Value Symbol Guard))
    (wholeBound : wholeCount ≤ fuel)
    (_wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
      start rest reader)
    (finishBound : finishUsed < wholeCount)
    (actual : Trace finishUsed (.code (.node rootRequest .pure))
      start
      (.code (.finishEdge handle row parentNext)) beforeFinish)
    (owner : beforeFinish.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      start)
    (past :
      Returned (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary request row
 := by
  intro originalQualified
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
      _querySmaller, _queryBound, queryPrefix, _actualDispatch, isolatedDispatch,
      queryPhysical, _queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin.actual_edge_query_dispatch_from_warm_query_finish
      rootRequest start initialPhysical fuel finishUsed handle request row parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      start
      ((Control.code (.edge request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.edge request .pure)) queryResume
      start queryBefore sourceHeap
      initialPhysical inputs fields operationsValid sourceGrowth queryOrigin (by omega)
  have observed := SourceCurrentAllocatedNativeCheckedEdgeBodyProfile.edge_body_children_profile_of_fuel_induction
    sourceHeap entry.identity request queryBefore beforeBody beforeFinish (fuel - queryUsed) bodyCount row
    (fun result => .finishEdge handle result (.pure result))
    queryPhysical queryGrowth queryOperations queryInputs queryFields isolatedDispatch (by omega) rawBody (by
      intro pair member used childFuel childCount _positive _childSmaller _childFuelBound
        _childCountBound childSpan next first last value origin _childPhysical _childGrowth
        _childOperations _childInputs _childFields _leftAvailable _rightAvailable childActual
      let child : NodeRequest Symbol Guard := ⟨request.domain, pair.1, pair.2⟩
      have qualified : Qualified (width := width) rootRequest start wholeCount
          entry body depth ordinary child := originalQualified pair member
      obtain ⟨childKey, keyed⟩ := qualified_key rootRequest start wholeCount
        entry body depth ordinary bodyCodec child qualified
      let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun result => (next result).bind queryResume
      have appended := origin.bind _ _ _ _ _ queryResume
      change Steps used (.code (.edge request queryResume)) queryBefore
        (.code (((requestNode request.domain pair.1 pair.2).bind next).bind queryResume)) first at appended
      have tail : Steps used (.code (.edge request queryResume)) queryBefore
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Code.bind_assoc, lifted] using appended
      have outer : Steps (queryUsed + used) (.code (.node rootRequest .pure))
          start
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first :=
        queryPrefix.steps.trans _ _ _ _ _ _ _ _ tail
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
        (NodeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        (EdgeResult (width := width) rootRequest start wholeCount entry body depth ordinary)
        rootRequest start initialPhysical fuel finishUsed (queryUsed + used) childCount
        (.code (.finishEdge handle row parentNext)) beforeFinish (by omega) actual past child childKey keyed
        lifted first last value (by omega) outer childActual
      rcases qualified with closed | mixed
      · exact currentLaw.1.1 closed
      · exact currentLaw.1.2 mixed)
  exact observed.1

end MicroCFTA.SourceCurrentNativeWarmEdgeFinish
