import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin
import MicroCFTA.SourceCurrentAllocatedNativeRowsPhysicalReadback
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixEdgeChildResult
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceCurrentAllocatedNativeRequestResults
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps

/-!
# Closed ordinary results at the same actual parent finish

The actual row walk bounds every child span by the observed body count.
The past edge law applies at this same parent before-finish state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceRecursiveIntersectionControl (decision)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified Qualified NodeResult EdgeResult)
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

theorem ordinary_payload (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    SourceRecursiveIntersectionControl.payload request.left request.right = .ordinary := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases first : SourceRecursiveIntersectionControl.identity request.left <;>
            cases second : SourceRecursiveIntersectionControl.identity request.right <;>
            simp only [first,second] at selected
          all_goals try cases selected
          split at selected
          · cases selected
          · exact selected

theorem ordinary_code [DecidableEq Symbol] (request : NodeRequest Symbol Guard)
    (selected : decision request.domain.key request.left request.right = .ordinary) :
    compileNode request = compileRows request.domain (InternedEdgeResidency.nodeEdges request.left) (InternedEdgeResidency.nodeEdges request.right) := by
  have payload := ordinary_payload request selected
  cases left : request.left <;> cases right : request.right <;>
    simp only [left,right,SourceRecursiveIntersectionControl.payload] at payload <;> try cases payload
  unfold compileNode
  simp only [selected]
  rw [left,right]
  rfl

theorem make_node_profile [DecidableEq (EdgeKey Symbol Guard)]
    (sourceName : Nat) (rows : List (EdgeValue Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (resident : ∀ row ∈ rows, EdgeResident heap row)
    (profiles : ∀ row ∈ rows, ∀ child ∈ row.children, Profile sourceName child) :
    Profile sourceName (run (makeNode rows) heap).1 := by
  refine ⟨?_, ?_⟩
  · rw [InternedNormalizationFree.makeNode_free rows heap facts.coherent facts.linked resident]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    obtain ⟨child, included, named⟩ :=
      (childFree_member ((canonicalEdges (surviving rows)).flatMap EdgeValue.children) name).mp member
    obtain ⟨row, selected, inRow⟩ := List.mem_flatMap.mp included
    have rawMember : row ∈ rows :=
      (List.mem_filter.mp (canonicalEdges_member (surviving rows) row selected)).1
    rw [(profiles row rawMember child inRow).1] at named
    cases named
  · intro atom occurrence
    have raw := InternedBoundaryAtoms.makeNode_atom_origin rows heap facts.coherent facts.linked resident atom occurrence
    obtain ⟨row, included, child, inRow, selected⟩ := (InternedBoundaryAtoms.edge_member rows atom).mp raw
    exact (profiles row included child inRow).2 atom selected

theorem all₂_row_profiles
    (sourceName : Nat) {jobs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard)}
    {rows : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (fun (_pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard)
      (row : EdgeValue Symbol Guard) => ∀ child ∈ row.children, Profile sourceName child) jobs rows) :
    ∀ row ∈ rows, ∀ child ∈ row.children, Profile sourceName child := by
  induction aligned with
  | nil =>
      intro row member
      cases member
  | cons head tail ih =>
      intro row member
      cases member with
      | head => exact head
      | tail _ included => exact ih row included

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

theorem closed_ordinary_profile_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (_accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (_built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (_stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
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
    (_wholeActual : Trace wholeCount (.code (.node rootRequest .pure))
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
    (qualified : ClosedQualified entry.identity request)
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
  have domainEmpty := closed_ordinary_domain entry.identity request qualified selected
  have originalPairsQualified : ∀ pair ∈ pairs (nodeEdges request.left) (nodeEdges request.right),
      ∀ children ∈ pair.1.children.zip pair.2.children,
        Qualified (width := width) rootRequest machine operations wholeCount entry body depth ordinary
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
      (⟨initial width machine, operations⟩ : Checked width)
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

end MicroCFTA.SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
