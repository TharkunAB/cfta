import MicroCFTA.SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin
import MicroCFTA.SourceCurrentAllocatedNativeSourceCanonicalOldEntry

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceEqualityNativeDemand
open SourceSynthesisUniversePrefixHeight (height)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
variable {width : Nat}
set_option autoImplicit false

def AuthenticEntryAt
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) : Prop :=
  pattern.free = [] ∧ SourceRecursiveIntersectionControl.identity pattern = some patternId ∧
    (SourceRecursiveIntersectionControl.tag pattern = 1 ∨ SourceRecursiveIntersectionControl.tag pattern = 3) ∧
    ∃ (universeFirst : Bool) (used : Nat) (before : Checked width)
      (next : Interned IntersectionFlatMemoKeyDomain.DomainKey → Code Symbol Guard (Value Symbol Guard)),
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let left := if universeFirst then universeValue else pattern
      let right := if universeFirst then pattern else universeValue
      let first := if universeFirst then entry.identity else patternId
      let second := if universeFirst then patternId else entry.identity
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
        IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
      let started : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := entered.2}}
      used + 1 ≤ wholeCount ∧
        Trace used (.code (.node rootRequest .pure)) start
          (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) before ∧
        SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
          IntersectionEmptyDomain.emptyKey left right first second = entered ∧
        Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain left right first second next)) before
          (.code (next entered.1)) started ∧ domain = entered.1

def MixedQualifiedAt
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) : Prop :=
  ∃ (pattern : Value Symbol Guard) (patternId : Nat) (openAlias operand : Value Symbol Guard),
    AuthenticEntryAt (width := width) rootRequest start wholeCount entry body depth ordinary
      pattern patternId request.domain ∧
    (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) ∧
    Profile entry.identity operand ∧ height operand ≤ height pattern ∧
    (openAlias = .reference (.interned entry.identity) → height operand < height pattern) ∧
    ((request.left = openAlias ∧ request.right = operand) ∨
      (request.left = operand ∧ request.right = openAlias))

theorem authentic_entry_at_initial
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (pattern : Value Symbol Guard) (patternId : Nat) (domain : Interned DomainKey) :
    AuthenticEntryAt rootRequest (⟨initial width machine, operations⟩ : Checked width)
      wholeCount entry body depth ordinary pattern patternId domain =
    SourceCurrentAllocatedNativeGeneralCMHistory.AuthenticEntry (width := width)
      rootRequest machine operations wholeCount entry body depth ordinary pattern patternId domain := rfl

theorem mixed_qualified_at_initial
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) :
    MixedQualifiedAt rootRequest (⟨initial width machine, operations⟩ : Checked width)
      wholeCount entry body depth ordinary request =
    SourceCurrentAllocatedNativeGeneralCMHistory.MixedQualified (width := width)
      rootRequest machine operations wholeCount entry body depth ordinary request := rfl

theorem stored_dispatch_issued_authentic_entry_at
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (caller : Caller width) (cached : EnumerationExpandableIndex.Cached Symbol Guard)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller cached)
    (source target sourceHandle targetHandle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (sourceStored : cached.core.values[source]? =
      some (.unenumerated (some sourceHandle) sourceScs))
    (targetStored : cached.core.values[target]? =
      some (.unenumerated (some targetHandle) targetScs))
    (rootRequest : NodeRequest Symbol Guard)
    (rootEmpty : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (sourceDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap sourceHandle = some rootRequest.left)
    (targetDecoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap targetHandle = some rootRequest.right)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid caller.checked.native)
    (queryUsed : Nat) (request : NodeRequest Symbol Guard)
    (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (queryBefore : Checked width)
    (issued : Trace queryUsed (.code (.node rootRequest .pure)) caller.checked
      (.code (.node request resume)) queryBefore)
    (oldRemaining : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (oldContinuation : Trace oldRemaining (.code (.node request resume)) queryBefore oldControl oldSnapshot)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (universeClosed : (Value.mu entry body depth ordinary).free = [])
    (pattern : Value Symbol Guard) (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : SourceRecursiveIntersectionControl.identity pattern = some patternId)
    (patternKind : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3)
    (universeFirst : Bool) (newRoot : NodeRequest Symbol Guard) (newUsed : Nat)
    (beforeNew reader : Checked width)
    (newNext : Interned DomainKey → Code Symbol Guard (Value Symbol Guard))
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
    AuthenticEntryAt rootRequest caller.checked (queryUsed + oldRemaining)
      entry body depth ordinary pattern patternId request.domain
 := by
  dsimp only
  intro newPrefix newEntry matchingKey
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let newEntered := SourceRecursiveIntersectionEnvironment.enter beforeNew.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  have oldWhole : Trace (queryUsed + oldRemaining) (.code (.node rootRequest .pure))
      caller.checked oldControl oldSnapshot := issued.trans oldContinuation
  have oldSnapshotPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldWhole physical).1
  have beforeNewPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension newPrefix oldSnapshotPhysical).1
  have newReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern patternClosed patternId patternIdentity patternKind universeFirst
    newNext 0 beforeNew reader newControl beforeNewPhysical newEntry
  obtain ⟨_newAllocation, _newStep, _newEvent, _newTail, _newHeap, _newCache, _newOperations,
      _universeBefore, _patternBefore, _universeReader, _patternReader, _startedDomain, _readerDomain,
      newKey, _newNonempty, _readerPhysical, _newGrowth, _classify⟩ := newReceipt
  have keyShape : request.domain.key = SourceRecursiveIntersectionDomain.extend
      IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) :=
    matchingKey.trans newKey
  obtain ⟨entryUsed, beforeOld, oldLeft, oldRight, oldFirst, oldSecond, oldNext,
      entryBound, rawPrefix, domainSame, rawEvent, rawSuffix, _leftClosed, _rightClosed,
      _leftIdentity, _rightIdentity, _pairSame⟩ :=
    SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin.stored_dispatch_issued_domain_enter_origin
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest rootEmpty sourceDecoded targetDecoded physical queryUsed request resume queryBefore issued
      entry.identity patternId keyShape
  let oldTail := queryUsed - (entryUsed + 1) + oldRemaining
  have oldSpan : Trace (oldTail + 1)
      (.code (.enter IntersectionEmptyDomain.emptyDomain oldLeft oldRight oldFirst oldSecond oldNext))
      beforeOld oldControl oldSnapshot := by
    have counts : 1 + (queryUsed - (entryUsed + 1) + oldRemaining) = oldTail + 1 := by
      dsimp only [oldTail]
      omega
    simpa only [counts] using rawEvent.trans (rawSuffix.trans oldContinuation)
  have equalKey : (SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
      IntersectionEmptyDomain.emptyDomain.key oldLeft oldRight oldFirst oldSecond).1.key = newEntered.1.key := by
    have rawKey : (SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
        IntersectionEmptyDomain.emptyKey oldLeft oldRight oldFirst oldSecond).1.key = newEntered.1.key :=
      (congrArg (fun domain : Interned DomainKey => domain.key) domainSame).symm.trans matchingKey
    simpa only [IntersectionEmptyDomain.emptyDomain] using rawKey
  have canonicalReceipt := SourceCurrentAllocatedNativeSourceCanonicalOldEntry.stored_dispatch_canonical_old_entry
    caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
    rootRequest rootEmpty sourceDecoded targetDecoded physical entryUsed beforeOld
    IntersectionEmptyDomain.emptyDomain oldLeft oldRight oldFirst oldSecond oldNext rawPrefix
    oldTail oldControl oldSnapshot oldSpan entry body depth ordinary universeClosed pattern patternClosed
    patternId patternIdentity patternKind universeFirst newRoot newUsed beforeNew reader newNext newControl
    newPrefix newEntry equalKey
  obtain ⟨oldUniverseFirst, _parentEmpty, canonicalPrefix, canonicalAllocation, _canonicalStep,
      canonicalEvent, _canonicalTail, _oldHeap, _oldCache, _oldOperations,
      _oldUniverseAvailable, _oldPatternAvailable, _oldStartedDomain, _oldSnapshotDomain, _oldKey⟩ := canonicalReceipt
  have controlSame := (Outcome.yielded.inj
    (rawPrefix.steps.execute.symm.trans canonicalPrefix.steps.execute)).1
  have argumentsSame := Code.enter.inj (Control.code.inj controlSame)
  have allocationSame : SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
      IntersectionEmptyDomain.emptyKey oldLeft oldRight oldFirst oldSecond =
      SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
        IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId := by
    rw [argumentsSame.2.1, argumentsSame.2.2.1, argumentsSame.2.2.2.1, argumentsSame.2.2.2.2.1]
    exact canonicalAllocation
  have domainCanonical : request.domain =
      (SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
        IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId).1 :=
    domainSame.trans (congrArg Prod.fst allocationSame)
  refine ⟨patternClosed, patternIdentity, patternKind, oldUniverseFirst, entryUsed, beforeOld, oldNext, ?_⟩
  dsimp only
  exact ⟨by omega, canonicalPrefix, canonicalAllocation, canonicalEvent, domainCanonical⟩

end MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry

#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt
#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.MixedQualifiedAt
#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.authentic_entry_at_initial
#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.mixed_qualified_at_initial
#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.stored_dispatch_issued_authentic_entry_at
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.authentic_entry_at_initial
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.mixed_qualified_at_initial
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry.stored_dispatch_issued_authentic_entry_at
