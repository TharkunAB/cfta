import MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
import MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

namespace MicroCFTA.SourceCurrentNativeWarmEdgeInitialProfile
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Old edge children at the same warm history]
The actual old edge body supplies each child request and returned value.
Its continuation reaches the same old snapshot. The keyed-child observer
retains that exact returned cell there. A later mixed qualifier supplies
an actual entry on the fixed full new trace. The cold-node source theorem
then gives the Profile of that same child value. The row is never replaced.
This proves an initial edge law. It does not prove meanings for new warm
cells or produce the four auxiliary initial laws.
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
    (newRoot : NodeRequest Symbol Guard) (oldSnapshot : Checked width) (newCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (request : NodeRequest Symbol Guard)
    (qualified : ClosedQualified entry.identity request ∨
      SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
        newRoot oldSnapshot newCount entry body depth ordinary request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases qualified with closed | mixed
  · exact key_of_codecs (width := width) request (closed_codec _ closed.1.1) (closed_codec _ closed.2.1.1)
  · obtain ⟨pattern, patternId, openAlias, operand, _authentic, aliasKind, operandProfile,
      _height, _strict, ordered⟩ := mixed
    have aliasCodec : ∃ input, IntersectionFlatMemoKey.input openAlias.referenceOf = some input := by
      rcases aliasKind with rfl | rfl
      · exact bodyCodec
      · exact ⟨.ref entry.identity, rfl⟩
    have operandCodec := closed_codec _ operandProfile.1
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact key_of_codecs (width := width) request (by rw [left]; exact aliasCodec)
        (by rw [right]; exact operandCodec)
    · exact key_of_codecs (width := width) request (by rw [left]; exact operandCodec)
        (by rw [right]; exact aliasCodec)

theorem cold_prefix_edges_qualified_for_actual_warm_history
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
    (oldLeftAvailable : Available machine.heap oldRoot.left)
    (oldRightAvailable : Available machine.heap oldRoot.right)
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
    (newActual : Trace newCount (.code (.node newRoot .pure))
      oldSnapshot newControl warmReader) :
    Returned (fun request row =>
      (∀ childPair ∈ request.left.children.zip request.right.children,
        SourceCurrentAllocatedNativeGeneralCMHistory.ClosedQualified entry.identity
            (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard) ∨
        SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
          newRoot oldSnapshot newCount entry body depth ordinary
          (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard)) →
      ∀ child ∈ row.children,
        SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity child)
      oldSnapshot.native.edges
 := by
  have oldGamma :=
    SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth operations operationsValid oldFuel oldCount oldControl oldSnapshot
      oldBound oldInputs oldFields oldActual
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyShape]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have universeClosed : (Value.mu entry body depth ordinary).free = [] := by
    rw [bodyShape]
    simp [Value.free]
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  intro handle request row oldCell originalQualified
  obtain ⟨finishUsed, suffixCount, beforeFinish, continuation, queryUsed, bodyCount,
      queryBefore, beforeBody, queryNext, finishTotal, _finishSmall, _finishFuel,
      _finishActual, _owner, _finishEvent, _finished, _suffix, queryTotal,
      _querySmall, _queryFuel, queryPrefix, _actualDispatch, isolatedDispatch,
      queryPhysical, _queryReady, _querySafe, _bodyOwner, rawBody, _nextSame, _admission⟩ :=
    SourceSynthesisCurrentUniverseNativeAllocation.original_universe_returned_edge_full_admission
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth pastInventory oldRootDomain
      oldLeftAvailable oldRightAvailable oldRootClosed.1 oldRootClosed.2
      operations oldFuel oldCount oldControl oldSnapshot oldBound oldActual handle request row oldCell
  have queryOrigin : Steps queryUsed (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      ((Control.code (.edge request .pure)).bind queryNext) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      oldFuel queryUsed (.code (.node oldRoot .pure)) (.code (.edge request .pure)) queryNext
      (⟨initial width machine, operations⟩ : Checked width) queryBefore sourceHeap
      initialPhysical oldInputs oldFields operationsValid sourceGrowth queryOrigin (by omega)
  have observed := SourceCurrentAllocatedNativeCheckedEdgeBodyProfile.edge_body_children_profile_of_fuel_induction
    sourceHeap entry.identity request queryBefore beforeBody beforeFinish (oldFuel - queryUsed) bodyCount row
    (fun result => .finishEdge handle result (.pure result))
    queryPhysical queryGrowth queryOperations queryInputs queryFields isolatedDispatch (by omega) rawBody (by
      intro pair member used childFuel childCount _positive _childSmaller _childFuelBound
        _childCountBound childSpan next first last value origin _childPhysical _childGrowth
        _childOperations _childInputs _childFields _leftAvailable _rightAvailable childActual
      let child : NodeRequest Symbol Guard := ⟨request.domain, pair.1, pair.2⟩
      have qualified : ClosedQualified entry.identity child ∨
          SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
            newRoot oldSnapshot newCount entry body depth ordinary child := originalQualified pair member
      obtain ⟨childKey, keyed⟩ := qualified_key newRoot oldSnapshot newCount
        entry body depth ordinary bodyCodec child qualified
      let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun result => (next result).bind queryNext
      have appended := origin.bind _ _ _ _ _ queryNext
      change Steps used (.code (.edge request queryNext)) queryBefore
        (.code (((requestNode request.domain pair.1 pair.2).bind next).bind queryNext)) first at appended
      have tail : Steps used (.code (.edge request queryNext)) queryBefore
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first := by
        simpa only [Code.bind_assoc, lifted] using appended
      have outer : Steps (queryUsed + used) (.code (.node oldRoot .pure))
          (⟨initial width machine, operations⟩ : Checked width)
          (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first :=
        queryPrefix.steps.trans _ _ _ _ _ _ _ _ tail
      have currentLaw := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_reader
        (NodeResult (width := width) oldRoot machine operations oldCount entry body depth ordinary)
        (EdgeResult (width := width) oldRoot machine operations oldCount entry body depth ordinary)
        oldRoot machine machineValid operations oldFuel oldCount (queryUsed + used) childCount
        oldControl oldSnapshot oldBound oldActual oldGamma.1 child childKey keyed
        lifted first last value (by omega) outer childActual
      obtain ⟨childHandle, _childReturned, childAtOld, _childSuffix, _childRetained⟩ := currentLaw.2
      rcases qualified with closed | mixed
      · exact currentLaw.1.1 closed
      ·
        obtain ⟨pattern, patternId, openAlias, operand, authentic,
          aliasKind, operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
        obtain ⟨patternClosed, patternIdentity, patternKind, universeFirst,
          entryUsed, beforeEntry, next, entryData⟩ := authentic
        dsimp only at entryData
        obtain ⟨entryBound, entryPrefix, _allocation, oneEntry, domainEq⟩ := entryData
        let universeValue : Value Symbol Guard := .mu entry body depth ordinary
        let entered := SourceRecursiveIntersectionEnvironment.enter beforeEntry.native.machine.domains
          IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
        let entering : Control (Value Symbol Guard) :=
          .code (.enter IntersectionEmptyDomain.emptyDomain
            (if universeFirst then universeValue else pattern)
            (if universeFirst then pattern else universeValue)
            (if universeFirst then entry.identity else patternId)
            (if universeFirst then patternId else entry.identity) next)
        let nextMachine : Machine Symbol Guard :=
          {beforeEntry.native.machine with domains := entered.2}
        let started : Checked width := {beforeEntry with native := advance beforeEntry.native nextMachine}
        have actualPrefix : Trace entryUsed (.code (.node newRoot .pure)) oldSnapshot entering beforeEntry :=
          entryPrefix
        have actualEntry : Trace 1 entering beforeEntry (.code (next entered.1)) started :=
          oneEntry
        have total : entryUsed + (newCount - entryUsed) = newCount := by omega
        have wholeTrace : Trace (entryUsed + (newCount - entryUsed))
            (.code (.node newRoot .pure)) oldSnapshot newControl warmReader := by
          simpa only [total] using newActual
        have prefixSplit := SourceCurrentHereditaryNativePhysicalSplit.split actualPrefix.steps wholeTrace
        have remaining : 1 + (newCount - entryUsed - 1) = newCount - entryUsed := by omega
        have fromEntry : Trace (1 + (newCount - entryUsed - 1))
            entering beforeEntry newControl warmReader := by
          simpa only [remaining] using prefixSplit.2
        have entrySplit := SourceCurrentHereditaryNativePhysicalSplit.split actualEntry.steps fromEntry
        have actualDomain : child.domain = entered.1 := domainEq
        have matchingKey : child.domain.key = entered.1.key :=
          congrArg (fun domain : Interned IntersectionFlatMemoKeyDomain.DomainKey => domain.key) actualDomain
        have result :=
          SourceCurrentAllocatedNativePastGammaEqualEntryPayload.closed_root_cold_returned_mixed_profile_after_later_entry
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            oldRoot machine oldRootDomain oldRootClosed universeClosed
            machineValid sourceGrowth operations operationsValid oldFuel oldCount oldControl
            oldSnapshot oldBound oldActual oldInputs oldFields childHandle child value childAtOld
            pattern patternClosed patternId patternIdentity patternKind universeFirst next newRoot newFuel entryUsed
            beforeEntry started (.code (next entered.1)) (by omega) prefixSplit.1 entrySplit.1 matchingKey
            openAlias operand aliasKind operandProfile operandHeight strictAlias ordered
        exact result.2.1
    )
  exact observed.1

end MicroCFTA.SourceCurrentNativeWarmEdgeInitialProfile
