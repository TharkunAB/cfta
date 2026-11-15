import MicroCFTA.SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
import MicroCFTA.SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification

/-!
# Original mixed ordinary results at the same parent finish

The original entry remains part of the fixed whole trace.
The source rows qualify each original zipped child pair.
The actual row walk bounds the edge calls by the parent body count.
The past edge law supplies each returned child profile.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralMOrdinaryFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision)
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
open SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
  (ordinary_payload ordinary_code make_node_profile all₂_row_profiles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

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
theorem mixed_ordinary_profile_at_actual_node_finish
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
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .ordinary)
    (qualified : MixedQualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary request)
    (past :
      Returned (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.edges) :
    Profile entry.identity value := by
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, queryBound, queryPrefix, actualDispatch, isolatedDispatch,
      queryPhysical, queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish
      rootRequest machine machineValid operations fuel finishUsed handle request value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      ((Control.code (.node request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node request .pure)) queryResume
      (⟨initial width machine, operations⟩ : Checked width) queryBefore sourceHeap
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
      (⟨initial width machine, operations⟩ : Checked width) rest reader := by
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
      (.code (.node rootRequest .pure)) (⟨initial width machine, operations⟩ : Checked width)
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
        Qualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary
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
      (⟨initial width machine, operations⟩ : Checked width)
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
          (⟨initial width machine, operations⟩ : Checked width)
          (.code ((requestEdge request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Control.bind, Code.bind_assoc, lifted] using bodyStart.trans _ _ _ _ _ _ _ _ appended
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixEdgeChildResult.edge_child_law_at_node_finish
        (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        rootRequest machine machineValid operations fuel finishUsed ((queryUsed + 1) + stepsBefore) rawCount
        handle value parentNext beforeFinish (by omega) actual past
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

end MicroCFTA.SourceCurrentAllocatedNativeGeneralMOrdinaryFinish
