import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistory
import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
import MicroCFTA.SourceEqualityNativeDemandMemo

set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionDomain (extend extend_seen)
open SourceEqualityNativeDemand
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntry MixedQualified)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

private theorem pair_fixed_left_injective (base left right : Nat)
    (same : pair base left = pair base right) : left = right := by
  simp only [pair, Prod.mk.injEq] at same
  omega

private theorem represented_same_key (cache : Cache.State DKey) (left right : Interned DKey)
    (leftKnown : IntersectionEmptyDomain.Represents cache left.key left)
    (rightKnown : IntersectionEmptyDomain.Represents cache right.key right)
    (sameKey : left.key = right.key) : left = right := by
  cases left with
  | mk leftId leftKey =>
    cases right with
    | mk rightId rightKey =>
      change leftKey = rightKey at sameKey
      subst rightKey
      have sameId : leftId = rightId := by
        by_cases empty : leftKey = IntersectionEmptyDomain.emptyKey
        · have first : leftId = 0 := by simpa only [empty, ite_true] using leftKnown.2
          have second : rightId = 0 := by simpa only [empty, ite_true] using rightKnown.2
          exact first.trans second.symm
        · have first : ∃ raw, cache.table leftKey = some raw ∧ leftId = raw.identity + 1 := by
            simpa only [empty, ite_false] using leftKnown.2
          have second : ∃ raw, cache.table leftKey = some raw ∧ rightId = raw.identity + 1 := by
            simpa only [empty, ite_false] using rightKnown.2
          obtain ⟨firstRaw, firstRead, firstId⟩ := first
          obtain ⟨secondRaw, secondRead, secondId⟩ := second
          have sameRaw : firstRaw = secondRaw := Option.some.inj (firstRead.symm.trans secondRead)
          cases sameRaw
          exact firstId.trans secondId.symm
      cases sameId
      rfl

theorem old_returned_mixed_profile_after_equal_key_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
    (oldPattern : Value Symbol Guard) (oldPatternId : Nat)
    (oldDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (oldAuthentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary oldPattern oldPatternId oldDomain)
    (inputs : InputsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (oldCell : oldSnapshot.native.nodes.cells handle = some ⟨request, .returned value⟩)
    (newPattern : Value Symbol Guard) (newClosed : newPattern.free = []) (newPatternId : Nat)
    (newIdentity : identity newPattern = some newPatternId)
    (newKind : SourceRecursiveIntersectionControl.tag newPattern = 1 ∨
      SourceRecursiveIntersectionControl.tag newPattern = 3)
    (universeFirst : Bool)
    (next : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard))
    (newRoot : NodeRequest Symbol Guard) (newFuel newUsed : Nat)
    (beforeNew reader : Checked width) (newControl : Control (Value Symbol Guard))
    (newBound : newUsed + 1 ≤ newFuel)
    (newPrefix : Trace newUsed (.code (.node newRoot .pure)) oldSnapshot
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else newPattern)
        (if universeFirst then newPattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else newPatternId)
        (if universeFirst then newPatternId else entry.identity) next)) beforeNew)
    (newEntry : Trace 1
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else newPattern)
        (if universeFirst then newPattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else newPatternId)
        (if universeFirst then newPatternId else entry.identity) next)) beforeNew newControl reader)
    (sameKey : (SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) newPattern
      entry.identity newPatternId).1.key = oldDomain.key)
    (domainMatches : request.domain =
      (SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
        IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) newPattern
        entry.identity newPatternId).1)
    (openAlias operand : Value Symbol Guard)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity operand)
    (operandHeight : SourceSynthesisUniversePrefixHeight.height operand ≤
      SourceSynthesisUniversePrefixHeight.height newPattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) →
      SourceSynthesisUniversePrefixHeight.height operand < SourceSynthesisUniversePrefixHeight.height newPattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias)) :
    oldPattern = newPattern ∧
    oldDomain = (SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) newPattern
      entry.identity newPatternId).1 ∧
    SourceSynthesisUniversePrefixHeight.height oldPattern = SourceSynthesisUniversePrefixHeight.height newPattern ∧
    SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value ∧
    reader.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
    Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader ∧
    newUsed + 1 ≤ newFuel := by
  have oldAuthForLaw := oldAuthentic
  have oldGamma :=
    SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth operations operationsValid fuel wholeCount oldControl oldSnapshot
      wholeBound inputs fields wholeActual
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical).1
  obtain ⟨oldClosed, oldIdentity, oldKind, oldUniverseFirst, oldUsed, beforeOld, oldNext, oldData⟩ := oldAuthentic
  dsimp only at oldData
  obtain ⟨oldBound, oldPrefix, _oldAllocation, _oldOne, oldDomainEq⟩ := oldData
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let oldEntered := SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue oldPattern entry.identity oldPatternId
  change oldDomain = oldEntered.1 at oldDomainEq
  have oldTotal : oldUsed + (wholeCount - oldUsed) = wholeCount := by omega
  have oldWhole : Trace (oldUsed + (wholeCount - oldUsed)) (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot := by
    simpa only [oldTotal] using wholeActual
  have oldSplit := SourceCurrentHereditaryNativePhysicalSplit.split oldPrefix.steps oldWhole
  have beforeOldPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldSplit.1 initialPhysical).1
  have oldLength : (wholeCount - oldUsed - 1) + 1 = wholeCount - oldUsed := by omega
  have oldSuffix : Trace ((wholeCount - oldUsed - 1) + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if oldUniverseFirst then universeValue else oldPattern)
        (if oldUniverseFirst then oldPattern else universeValue)
        (if oldUniverseFirst then entry.identity else oldPatternId)
        (if oldUniverseFirst then oldPatternId else entry.identity) oldNext)) beforeOld oldControl oldSnapshot := by
    simpa only [oldLength] using oldSplit.2
  have oldReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary oldPattern oldClosed oldPatternId oldIdentity oldKind oldUniverseFirst
    oldNext (wholeCount - oldUsed - 1) beforeOld oldSnapshot oldControl beforeOldPhysical oldSuffix
  obtain ⟨_oldCanonical, _oldStep, _oldChecked, _oldTail, _oldHeap, _oldCache, _oldOperations,
      _oldUBefore, _oldPBefore, _oldUAfter, oldAvailable, _oldStartedDomain,
      oldKnown, oldKey, _oldNonempty, _oldReaderPhysical, _oldExtension, _oldClassify⟩ := oldReceipt
  have oldDomainKnown : Domain oldSnapshot.native.machine oldDomain := by
    rw [oldDomainEq]
    exact oldKnown
  have oldDomainKey : oldDomain.key = extend IntersectionEmptyDomain.emptyKey
      [entry.identity] (pair entry.identity oldPatternId) := by
    rw [oldDomainEq]
    exact oldKey
  have beforeNewPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension newPrefix oldPhysical).1
  have newReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary newPattern newClosed newPatternId newIdentity newKind universeFirst
    next 0 beforeNew reader newControl beforeNewPhysical newEntry
  obtain ⟨_newCanonical, _newStep, _newChecked, _newTail, _newHeap, _newCache, _newOperations,
      _newUBefore, _newPBefore, _newUAfter, newAvailable, _newStartedDomain,
      newKnown, newKey, _newNonempty, _newReaderPhysical, _newExtension, _newClassify⟩ := newReceipt
  let newEntered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue newPattern entry.identity newPatternId
  change newEntered.1.key = oldDomain.key at sameKey
  change request.domain = newEntered.1 at domainMatches
  change newEntered.1.key = extend IntersectionEmptyDomain.emptyKey [entry.identity]
    (pair entry.identity newPatternId) at newKey
  have warmSpan : Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader :=
    newPrefix.trans newEntry
  have reached := SourceCurrentNativeEnterCommonOperand.checked_trace_extension warmSpan oldPhysical
  have oldAtReader : Available reader.native.machine.heap oldPattern :=
    reached.2.available oldPattern oldAvailable
  have oldDomainAtReader : Domain reader.native.machine oldDomain :=
    SourceRecursiveIntersectionKernel.Domain.grows oldDomain oldDomainKnown reached.2
  have oldPairMember : pair entry.identity oldPatternId ∈ oldDomain.key.seen := by
    rw [oldDomainKey]
    exact (extend_seen IntersectionEmptyDomain.emptyKey [entry.identity]
      (pair entry.identity oldPatternId) (pair entry.identity oldPatternId)).2 (Or.inl rfl)
  have newPairMember : pair entry.identity oldPatternId ∈ newEntered.1.key.seen := by
    simpa only [sameKey] using oldPairMember
  rw [newKey] at newPairMember
  have pairEq : pair entry.identity oldPatternId = pair entry.identity newPatternId := by
    rcases (extend_seen IntersectionEmptyDomain.emptyKey [entry.identity]
      (pair entry.identity newPatternId) (pair entry.identity oldPatternId)).1 newPairMember with equal | absent
    · exact equal
    · cases absent
  have samePatternId : oldPatternId = newPatternId :=
    pair_fixed_left_injective entry.identity oldPatternId newPatternId pairEq
  have patternEq : oldPattern = newPattern :=
    SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective
      reader.native.machine.heap reached.1.machine.1 oldPattern newPattern oldAtReader newAvailable
      oldClosed newClosed oldPatternId oldIdentity (by simpa only [samePatternId] using newIdentity)
  have domainsEq : oldDomain = newEntered.1 :=
    represented_same_key reader.native.machine.domains oldDomain newEntered.1
      oldDomainAtReader.represented newKnown.represented sameKey.symm
  have actualDomain : request.domain = oldDomain := domainMatches.trans domainsEq.symm
  have qualified : MixedQualified (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary request := by
    refine ⟨oldPattern, oldPatternId, openAlias, operand, ?_, aliasKind, operandProfile, ?_, ?_, ordered⟩
    · simpa only [actualDomain] using oldAuthForLaw
    · simpa only [patternEq] using operandHeight
    · intro referenceAlias
      simpa only [patternEq] using strictAlias referenceAlias
  have profile : SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value :=
    (oldGamma.1.1 handle request value oldCell).2 qualified
  have retention := SourceEqualityNativeDemandMemo.execute_preserves
    (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot oldPhysical.shape
  have retained : SourceEqualityNativeDemandMemo.Retained oldSnapshot.native reader.native := by
    simpa only [warmSpan.steps.execute, Outcome.state] using retention.2
  exact ⟨patternEq, domainsEq, congrArg height patternEq, profile,
    retained.nodes handle request value oldCell, warmSpan, newBound⟩

end MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

#check MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload.old_returned_mixed_profile_after_equal_key_entry
#print axioms MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload.old_returned_mixed_profile_after_equal_key_entry
