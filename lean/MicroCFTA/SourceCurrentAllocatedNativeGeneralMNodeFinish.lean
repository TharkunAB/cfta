import MicroCFTA.SourceCurrentAllocatedNativeGeneralCNodeFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralMOrdinaryFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralMUnionFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish
import MicroCFTA.SourceCurrentAllocatedNativeAuthenticBodyFirstOuterFinish
import MicroCFTA.SourceCurrentAllocatedNativeAuthenticDiagonalOuterFinish
import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

/-!
# All original mixed node cases at the same actual finish

The full original pattern stays on the same checked history.
The child laws hold at the exact state before the parent finish.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGeneralMNodeFinish
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (decision payload identity tag pair)
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

theorem mixed_result_at_actual_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyId)
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
    (pattern : Node) (patternId : Nat) (openAlias operand : Node)
    (authentic : AuthenticEntry (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary pattern patternId request.domain)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : Profile entry.identity operand)
    (operandHeight : height operand ≤ height pattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) → height operand < height pattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))
    (past :
      Returned (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
        beforeFinish.native.nodes ∧
      Returned (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
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
  have qualified : MixedQualified (width := width) rootRequest machine operations wholeCount
      entry body depth ordinary request :=
    ⟨pattern, patternId, openAlias, operand, authentic, aliasKind,
      operandProfile, operandHeight, strictAlias, ordered⟩
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
      _querySmaller, _queryBound, queryPrefix, actualDispatch, _isolatedDispatch,
      queryPhysical, queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
    SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish
      rootRequest machine machineValid operations fuel finishUsed handle request value parentNext
      beforeFinish (by omega) actual owner
  have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      ((Control.code (.node request .pure)).bind queryResume) queryBefore := by
    simpa only [Control.bind, Code.bind] using queryPrefix.steps
  obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, _queryOperations,
      _queryOperationsGrowth, _queryBoundInputs, _queryInputs, _queryBoundFields, _queryFields⟩ :=
    SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
      fuel queryUsed (.code (.node rootRequest .pure)) (.code (.node request .pure)) queryResume
      (⟨initial width machine, operations⟩ : Checked width) queryBefore sourceHeap
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
      (⟨initial width machine, operations⟩ : Checked width)
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
    have childQualified : MixedQualified (width := width) rootRequest machine operations wholeCount
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
        (⟨initial width machine, operations⟩ : Checked width)
        (.code ((requestNode child.domain child.left child.right).bind
          (fun result => .finishNode handle result (queryResume result)))) beforeBody := by
      simpa only [compiled] using bodyStart.steps
    have childActual : Steps bodyCount (.code (requestNode child.domain child.left child.right)) beforeBody
        (.code (.pure value)) beforeFinish := by
      simpa only [compiled] using rawBody
    obtain ⟨childKey, keyed⟩ := SourceCurrentAllocatedNativeGeneralCMHistory.qualified_key
      rootRequest machine operations wholeCount entry body depth ordinary bodyCodec child (Or.inr childQualified)
    have law := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_node_finish
      (NodeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
      (EdgeResult (width := width) rootRequest machine operations wholeCount entry body depth ordinary)
      rootRequest machine machineValid operations fuel finishUsed (queryUsed + 1) bodyCount handle value parentNext
      beforeFinish (by omega) actual past child childKey keyed
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
      (⟨initial width machine, operations⟩ : Checked width) rest reader := by
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
      exact SourceCurrentAllocatedNativeGeneralMUnionFinish.mixed_union_profile_at_actual_node_finish
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        rootRequest machine machineValid sourceGrowth operations operationsValid fuel wholeCount finishUsed handle
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
        exact SourceCurrentAllocatedNativeGeneralMOrdinaryFinish.mixed_ordinary_profile_at_actual_node_finish
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          rootRequest machine machineValid sourceGrowth operations operationsValid fuel wholeCount finishUsed handle
          request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
          inputs fields selected qualified past
      · subst openAlias
        rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
        · exact SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish.mixed_reference_node_profile_at_actual_node_finish
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            rootRequest machine machineValid sourceGrowth operations operationsValid fuel wholeCount finishUsed handle
            request value rest reader beforeFinish parentNext wholeBound wholeActual finishBound actual owner
            inputs fields true own rows level ⟨left, right⟩ qualified past
        · exact SourceCurrentAllocatedNativeGeneralMReferenceNodeFinish.mixed_reference_node_profile_at_actual_node_finish
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            rootRequest machine machineValid sourceGrowth operations operationsValid fuel wholeCount finishUsed handle
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
          have valueEq := SourceCurrentAllocatedNativeAuthenticBodyFirstOuterFinish.body_first_outer_finish_of_past_body_first_key_law
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            bodyId bodyIdentity rootRequest machine machineValid operations operationsValid sourceGrowth
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
          have valueEq := SourceCurrentAllocatedNativeAuthenticDiagonalOuterFinish.diagonal_outer_finish_of_past_coherent_laws
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            bodyId bodyIdentity rootRequest machine machineValid operations operationsValid sourceGrowth
            fuel wholeCount finishUsed pattern patternId request.domain request.domain originalEntry rfl
            handle value parentNext beforeFinish rest reader wholeBound wholeActual (by omega) actual held
            inputs fields innerPast.2.2
          rw [valueEq]
          exact universeProfile

end MicroCFTA.SourceCurrentAllocatedNativeGeneralMNodeFinish
