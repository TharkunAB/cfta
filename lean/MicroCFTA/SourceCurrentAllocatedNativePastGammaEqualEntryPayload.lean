import MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry
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

/- Note [Warm entry identity transport]
The earlier producing query can start with inherited memo tables.
Its actual trace and authentic entry retain the complete old pattern.
The later literal equal-key entry supplies the same-reader comparison.
Reuse the checked common-reader and represented-domain proofs here.
This lemma proves identity transport. It does not supply the earlier
source qualification or a semantic law for the returned payload.
-/

/-- The same actual warm reader identifies complete patterns at equal-key entries. -/
theorem old_warm_entry_full_pattern_after_equal_key_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (oldRoot : NodeRequest Symbol Guard) (oldStart : Checked width)
    (initialPhysical : Physical oldStart.native)
    (wholeCount : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure)) oldStart oldControl oldSnapshot)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (oldPattern : Value Symbol Guard) (oldPatternId : Nat)
    (oldDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (oldAuthentic : SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt
      (width := width) oldRoot oldStart wholeCount
      entry body depth ordinary oldPattern oldPatternId oldDomain)
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
      entry.identity newPatternId).1.key = oldDomain.key) :
    oldPatternId = newPatternId ∧
    oldPattern = newPattern ∧
    oldDomain = (SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) newPattern
      entry.identity newPatternId).1 ∧
    height oldPattern = height newPattern ∧
    Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader ∧
    newUsed + 1 ≤ newFuel := by
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
      oldStart oldControl oldSnapshot := by
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
  exact ⟨samePatternId, patternEq, domainsEq, congrArg height patternEq, warmSpan, newBound⟩

end MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

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

/- Note [Closed-root returned entry recovery]
The actual source query starts with closed operands at the empty domain.
A returned cell is either inherited or produced by that same query.
Its literal dispatch and a later matching entry identify the old source entry.
Empty initial tables remove the inherited alternative in the cold source case.
The input operand qualification remains explicit. This result does not derive
all qualifications for an arbitrary worker history.
-/

/-- Recover the actual old entry without two enumeration-slot lookups. -/
theorem closed_root_returned_or_authentic_entry_at
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (before : Checked width) (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (rootClosed : rootRequest.left.free = [] ∧ rootRequest.right.free = [])
    (physical : Physical before.native)
    (fuel wholeCount : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (bounded : wholeCount ≤ fuel)
    (actual : Trace wholeCount (.code (.node rootRequest .pure)) before oldControl oldSnapshot)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (returned : oldSnapshot.native.nodes.cells handle = some ⟨request, .returned value⟩)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (universeClosed : (Value.mu entry body depth ordinary).free = [])
    (pattern : Value Symbol Guard) (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId)
    (patternKind : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3)
    (universeFirst : Bool) (newRoot : NodeRequest Symbol Guard) (newUsed : Nat)
    (beforeNew reader : Checked width)
    (newNext : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard))
    (newControl : Control (Value Symbol Guard)) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let newLeft := if universeFirst then universeValue else pattern
    let newRight := if universeFirst then pattern else universeValue
    let newFirst := if universeFirst then entry.identity else patternId
    let newSecond := if universeFirst then patternId else entry.identity
    let newEntered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    Trace newUsed (.code (.node newRoot .pure)) oldSnapshot
      (.code (.enter IntersectionEmptyDomain.emptyDomain newLeft newRight newFirst newSecond newNext)) beforeNew →
    Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain newLeft newRight newFirst newSecond newNext))
      beforeNew newControl reader →
    request.domain.key = newEntered.1.key →
    before.native.nodes.cells handle = some ⟨request, .returned value⟩ ∨
      (SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt rootRequest before wholeCount
        entry body depth ordinary pattern patternId request.domain ∧
       ∃ (queryUsed : Nat) (queryBefore : Checked width)
         (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
         queryUsed < wholeCount ∧ queryUsed < fuel ∧
         Trace queryUsed (.code (.node rootRequest .pure)) before
           (.code (.node request resume)) queryBefore) := by
  dsimp only
  intro newPrefix newEntry matchingKey
  rcases SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_or_finish_prefix actual
      handle request value returned with retained | produced
  · exact Or.inl retained
  · obtain ⟨finishUsed, suffixCount, beforeFinish, continuation, total, finishPrefix,
        running, _finishEvent, _finished, _finishSuffix⟩ := produced
    obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, countsToFinish,
        queryBeforeFinish, queryFuel, issued, _queryEvent, _isolatedEvent,
        _queryPhysical, _queryReady, _queryKey, _bodyRunning, _bodyTrace, _last⟩ :=
      SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
        rootRequest before physical fuel finishUsed handle request value continuation beforeFinish
        (by omega) finishPrefix running
    have queryBeforeWhole : queryUsed < wholeCount := by omega
    have counts : queryUsed + (wholeCount - queryUsed) = wholeCount := by omega
    have wholeReindexed : Trace (queryUsed + (wholeCount - queryUsed))
        (.code (.node rootRequest .pure)) before oldControl oldSnapshot := by
      simpa only [counts] using actual
    have parts := SourceCurrentHereditaryNativePhysicalSplit.split issued.steps wholeReindexed
    have authenticated :=
      SourceCurrentAllocatedNativeSourceWarmEntry.closed_root_issued_authentic_entry_at
        before rootRequest rootEmpty rootClosed physical queryUsed request resume queryBefore issued
        (wholeCount - queryUsed) oldControl oldSnapshot parts.2 entry body depth ordinary universeClosed
        pattern patternClosed patternId patternIdentity patternKind universeFirst newRoot newUsed beforeNew
        reader newNext newControl newPrefix newEntry matchingKey
    apply Or.inr
    refine ⟨?_, queryUsed, queryBefore, resume, queryBeforeWhole, queryFuel, issued⟩
    simpa only [counts] using authenticated

/-- Derive the old cold-source result profile without an assumed old entry. -/
theorem closed_root_cold_returned_mixed_profile_after_later_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (rootEmpty : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (rootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (universeClosed : (Value.mu entry body depth ordinary).free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel wholeCount : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (wholeActual : Trace wholeCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
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
    (matchingKey : request.domain.key =
      (SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
        IntersectionEmptyDomain.emptyKey (.mu entry body depth ordinary) newPattern
        entry.identity newPatternId).1.key)
    (openAlias operand : Value Symbol Guard)
    (aliasKind : openAlias = body ∨ openAlias = .reference (.interned entry.identity))
    (operandProfile : SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity operand)
    (operandHeight : SourceSynthesisUniversePrefixHeight.height operand ≤
      SourceSynthesisUniversePrefixHeight.height newPattern)
    (strictAlias : openAlias = .reference (.interned entry.identity) →
      SourceSynthesisUniversePrefixHeight.height operand < SourceSynthesisUniversePrefixHeight.height newPattern)
    (ordered : (request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias)) :
    AuthenticEntry (width := width) oldRoot machine operations wholeCount
      entry body depth ordinary newPattern newPatternId request.domain ∧
    SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value ∧
    reader.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
    Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader ∧
    newUsed + 1 ≤ newFuel := by
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have recovered := closed_root_returned_or_authentic_entry_at
    (⟨initial width machine, operations⟩ : Checked width) oldRoot rootEmpty rootClosed initialPhysical
    fuel wholeCount oldControl oldSnapshot wholeBound wholeActual handle request value oldCell
    entry body depth ordinary universeClosed newPattern newClosed newPatternId newIdentity newKind
    universeFirst newRoot newUsed beforeNew reader next newControl newPrefix newEntry matchingKey
  rcases recovered with retained | produced
  · have impossible : (none : Option (FlatMemoThunk.Cell
        (NodeRequest Symbol Guard) (Value Symbol Guard))) = some ⟨request, .returned value⟩ := retained
    cases impossible
  · obtain ⟨authentic, _issued⟩ := produced
    have oldAuthentic : AuthenticEntry (width := width) oldRoot machine operations wholeCount
        entry body depth ordinary newPattern newPatternId request.domain := authentic
    have qualified : MixedQualified (width := width) oldRoot machine operations wholeCount
        entry body depth ordinary request :=
      ⟨newPattern, newPatternId, openAlias, operand, oldAuthentic, aliasKind,
        operandProfile, operandHeight, strictAlias, ordered⟩
    have oldGamma :=
      SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldRoot machine machineValid sourceGrowth operations operationsValid fuel wholeCount oldControl oldSnapshot
        wholeBound inputs fields wholeActual
    have profile : SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity value :=
      (oldGamma.1.1 handle request value oldCell).2 qualified
    have warmSpan : Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader :=
      newPrefix.trans newEntry
    have oldPhysical :=
      (SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical).1
    have retention := SourceEqualityNativeDemandMemo.execute_preserves
      (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot oldPhysical.shape
    have kept : SourceEqualityNativeDemandMemo.Retained oldSnapshot.native reader.native := by
      simpa only [warmSpan.steps.execute, Outcome.state] using retention.2
    exact ⟨oldAuthentic, profile, kept.nodes handle request value oldCell, warmSpan, newBound⟩

end MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload

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
set_option autoImplicit false

/- Note [One old edge and all later qualifications]
The old cold query supplies one returned row law. Every mixed input of that
row is rebased to the same original entry and full pattern. Its later entry
comes from the same complete warm trace, including entries after earlier hits.
Split that trace at the literal entry before applying identity transport.
Closed qualifications pass through unchanged. Input qualifications remain an
internal EdgeResult contract. This proof does not derive them for worker calls.
-/

theorem old_returned_edge_profiles_after_equal_key_entries
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
    (handle : Nat) (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard)
    (oldCell : oldSnapshot.native.edges.cells handle = some ⟨request, .returned row⟩)
    (domainKeyMatches : request.domain.key = oldDomain.key)
    (newRoot : NodeRequest Symbol Guard) (newFuel newCount : Nat)
    (newControl : Control (Value Symbol Guard)) (reader : Checked width)
    (newBound : newCount ≤ newFuel)
    (newActual : Trace newCount (.code (.node newRoot .pure)) oldSnapshot newControl reader)
    (childQualifications : ∀ childPair ∈ request.left.children.zip request.right.children,
      SourceCurrentAllocatedNativeGeneralCMHistory.ClosedQualified entry.identity
          (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard) ∨
        SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt (width := width)
          newRoot oldSnapshot newCount entry body depth ordinary
          (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard)) :
    (∀ childPair ∈ request.left.children.zip request.right.children,
      SourceCurrentAllocatedNativeGeneralCMHistory.Qualified (width := width)
        oldRoot machine operations wholeCount entry body depth ordinary
        (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard)) ∧
    (∀ child ∈ row.children,
      SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity child) ∧
    reader.native.edges.cells handle = some ⟨request, .returned row⟩ ∧
    Trace newCount (.code (.node newRoot .pure)) oldSnapshot newControl reader ∧
    newCount ≤ newFuel := by
  have oldGamma :=
    SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine machineValid sourceGrowth operations operationsValid fuel wholeCount oldControl oldSnapshot
      wholeBound inputs fields wholeActual
  have initialPhysical : Physical (initial width machine) :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have oldPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension wholeActual initialPhysical).1
  have oldAuthAt : SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
      oldRoot (⟨initial width machine, operations⟩ : Checked width) wholeCount
      entry body depth ordinary oldPattern oldPatternId oldDomain := by
    simpa only [SourceCurrentAllocatedNativeSourceWarmEntry.authentic_entry_at_initial] using oldAuthentic
  have rebased : ∀ childPair ∈ request.left.children.zip request.right.children,
      SourceCurrentAllocatedNativeGeneralCMHistory.Qualified (width := width)
        oldRoot machine operations wholeCount entry body depth ordinary
        (⟨request.domain, childPair.1, childPair.2⟩ : NodeRequest Symbol Guard) := by
    intro childPair member
    rcases childQualifications childPair member with closed | mixed
    · exact Or.inl closed
    · right
      obtain ⟨newPattern, newPatternId, openAlias, operand, authentic,
        aliasKind, operandProfile, operandHeight, strictAlias, ordered⟩ := mixed
      obtain ⟨newClosed, newIdentity, newKind, universeFirst, newUsed, beforeNew, next, newData⟩ := authentic
      dsimp only at newData
      obtain ⟨entryBound, newPrefix, _newAllocation, newEntry, domainEq⟩ := newData
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let newEntered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
        IntersectionEmptyDomain.emptyKey universeValue newPattern entry.identity newPatternId
      let entering : Control (Value Symbol Guard) :=
        .code (.enter IntersectionEmptyDomain.emptyDomain
          (if universeFirst then universeValue else newPattern)
          (if universeFirst then newPattern else universeValue)
          (if universeFirst then entry.identity else newPatternId)
          (if universeFirst then newPatternId else entry.identity) next)
      let started : Checked width :=
        {beforeNew with native := advance beforeNew.native {beforeNew.native.machine with domains := newEntered.2}}
      have prefixTrace : Trace newUsed (.code (.node newRoot .pure)) oldSnapshot entering beforeNew :=
        newPrefix
      have entryTrace : Trace 1 entering beforeNew (.code (next newEntered.1)) started :=
        newEntry
      have total : newUsed + (newCount - newUsed) = newCount := by omega
      have full : Trace (newUsed + (newCount - newUsed))
          (.code (.node newRoot .pure)) oldSnapshot newControl reader := by
        simpa only [total] using newActual
      have separated := SourceCurrentHereditaryNativePhysicalSplit.split prefixTrace.steps full
      have remaining : 1 + (newCount - newUsed - 1) = newCount - newUsed := by omega
      have fromEntry : Trace (1 + (newCount - newUsed - 1)) entering beforeNew newControl reader := by
        simpa only [remaining] using separated.2
      have atEntry := SourceCurrentHereditaryNativePhysicalSplit.split entryTrace.steps fromEntry
      have actualDomain : request.domain = newEntered.1 := domainEq
      have sameKey : newEntered.1.key = oldDomain.key :=
        (congrArg (fun domain : Interned DKey => domain.key) actualDomain).symm.trans domainKeyMatches
      have identified := old_warm_entry_full_pattern_after_equal_key_entry
        oldRoot (⟨initial width machine, operations⟩ : Checked width) initialPhysical
        wholeCount oldControl oldSnapshot wholeActual entry body depth ordinary
        oldPattern oldPatternId oldDomain oldAuthAt
        newPattern newClosed newPatternId newIdentity newKind universeFirst next
        newRoot newFuel newUsed beforeNew started (.code (next newEntered.1))
        (by omega) separated.1 atEntry.1 sameKey
      obtain ⟨_samePatternId, patternEq, domainsEq, _sameHeight, _entrySpan, _entryBound⟩ := identified
      have actualOldDomain : request.domain = oldDomain := actualDomain.trans domainsEq.symm
      refine ⟨oldPattern, oldPatternId, openAlias, operand, ?_, aliasKind, operandProfile, ?_, ?_, ordered⟩
      · simpa only [actualOldDomain] using oldAuthentic
      · simpa only [patternEq] using operandHeight
      · intro referenceAlias
        simpa only [patternEq] using strictAlias referenceAlias
  have profiles : ∀ child ∈ row.children,
      SourceCurrentAllocatedNativeClosedResetProfile.Profile entry.identity child :=
    (oldGamma.1.2 handle request row oldCell) rebased
  have retention := SourceEqualityNativeDemandMemo.execute_preserves
    newCount (.code (.node newRoot .pure)) oldSnapshot oldPhysical.shape
  have retained : SourceEqualityNativeDemandMemo.Retained oldSnapshot.native reader.native := by
    simpa only [newActual.steps.execute, Outcome.state] using retention.2
  exact ⟨rebased, profiles, retained.edges handle request row oldCell, newActual, newBound⟩

end MicroCFTA.SourceCurrentAllocatedNativePastGammaEqualEntryPayload
