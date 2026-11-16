import MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEdgeEntry
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}
set_option autoImplicit false

theorem stored_dispatch_issued_edge_authentic_entry_at
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
    (queryUsed : Nat) (request : EdgeRequest Symbol Guard)
    (resume : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (queryBefore : Checked width)
    (issued : Trace queryUsed (.code (.node rootRequest .pure)) caller.checked
      (.code (.edge request resume)) queryBefore)
    (oldRemaining : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (oldContinuation : Trace oldRemaining (.code (.edge request resume)) queryBefore oldControl oldSnapshot)
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
    SourceCurrentAllocatedNativeSourceIssuedDomainEnterOrigin.stored_dispatch_issued_edge_domain_enter_origin
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

end MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEdgeEntry

#check MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEdgeEntry.stored_dispatch_issued_edge_authentic_entry_at
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEdgeEntry.stored_dispatch_issued_edge_authentic_entry_at
