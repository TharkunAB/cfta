import MicroCFTA.SourceCurrentAllocatedNativeGeneralCOrdinaryFinish
import MicroCFTA.SourceCurrentAllocatedNativeMixedUnionProfile
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult

/-!
# Original mixed union results from the same actual past law

The original full pattern and actual entry stay on the whole fixed trace.
The raw union producer supplies actual ordered child count bounds.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish
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
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

theorem mixed_union_profile_at_actual_node_finish
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
    (unionOperand : ∃ (unionEntry : Interned NodeKey) (members : List Node) (level : Nat) (free : List Reference),
      request.left = .union unionEntry members level free ∨
        request.right = .union unionEntry members level free)
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
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _sourceFacts⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
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
    (.code (.node rootRequest .pure)) (⟨initial width machine, operations⟩ : Checked width)
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
  have childQualified : MixedQualified (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary child := by
    refine ⟨pattern, patternId, alias, closedOperand, ?_, aliasChoice, ownProfile,
      childHeight, strictChild, orderedChild⟩
    rw [childDomain]
    exact originalEntry
  obtain ⟨childKey, keyed⟩ := SourceCurrentAllocatedNativeGeneralCMHistory.qualified_key
    rootRequest machine operations wholeCount entry body depth ordinary bodyCodec child (Or.inr childQualified)
  have lifted := origin.bind _ _ _ _ _ queryResume
  have globalOrigin : Steps (queryUsed + used) (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind
        (fun result => (next result).bind queryResume))) first := by
    simpa only [Control.bind, Code.bind_assoc] using
      queryOrigin.trans _ _ _ _ _ _ _ _ lifted
  have observed := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
    (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
    rootRequest machine machineValid operations fuel finishUsed (queryUsed + used) childCount
    handle value parentNext beforeFinish (by omega) actual past child childKey keyed
    (fun result => (next result).bind queryResume) first last emitted (by omega) globalOrigin childActual
  exact observed.1.2 childQualified

end MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish

#check @MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish.mixed_union_profile_at_actual_node_finish
#print axioms MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish.mixed_union_profile_at_actual_node_finish
