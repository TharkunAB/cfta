import MicroCFTA.SourceCurrentAllocatedNativeSourceEmptyEnterOperands
import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceEnterFullOperands
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open InternedProbeProvenance SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}
set_option autoImplicit false

/-- Actual source entries with the same full key have the same closed full operands. -/
theorem stored_dispatch_old_new_full_operands
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
    (oldUsed : Nat) (beforeOld : Checked width) (parent : Interned DomainKey)
    (oldLeft oldRight : Value Symbol Guard) (oldFirst oldSecond : Nat)
    (oldNext : Interned DomainKey → Code Symbol Guard (Value Symbol Guard))
    (oldPrefix : Trace oldUsed (.code (.node rootRequest .pure)) caller.checked
      (.code (.enter parent oldLeft oldRight oldFirst oldSecond oldNext)) beforeOld)
    (oldTail : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (oldSpan : Trace (oldTail + 1)
      (.code (.enter parent oldLeft oldRight oldFirst oldSecond oldNext)) beforeOld oldControl oldSnapshot)
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
    (SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
      parent.key oldLeft oldRight oldFirst oldSecond).1.key = newEntered.1.key →
    parent.key = IntersectionEmptyDomain.emptyKey ∧
      ((oldLeft = universeValue ∧ oldRight = pattern) ∨
       (oldLeft = pattern ∧ oldRight = universeValue)) ∧
      Available reader.native.machine.heap oldLeft ∧ Available reader.native.machine.heap oldRight ∧
      Available reader.native.machine.heap universeValue ∧ Available reader.native.machine.heap pattern := by
  dsimp only
  intro newPrefix newEntry sameKey
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have beforeOldPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldPrefix physical).1
  have oldReceipt := SourceCurrentNativeEnterCommonOperand.enter_prefix_common_operands
    parent oldLeft oldRight oldFirst oldSecond oldNext oldTail beforeOld oldSnapshot oldControl
    beforeOldPhysical oldSpan
  obtain ⟨_oldStep, _oldSuffix, _oldHeap, _oldCache, _oldOperations, _oldDomain,
      _oldLeftBefore, _oldRightBefore, oldLeftAvailable, oldRightAvailable,
      _oldStartedDomain, _oldReachedDomain, _oldKey, _oldExtension, _oldClassify⟩ := oldReceipt
  have oldSnapshotPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension oldSpan beforeOldPhysical).1
  have beforeNewPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension newPrefix oldSnapshotPhysical).1
  have newReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern patternClosed patternId patternIdentity patternKind universeFirst
    newNext 0 beforeNew reader newControl beforeNewPhysical newEntry
  obtain ⟨_newCanonical, _newStep, _newChecked, _newSuffix, _newHeap, _newCache, _newOperations,
      _newUBefore, _newPBefore, universeAvailable, patternAvailable, _newStartedDomain,
      _newReachedDomain, newKey, _newNonempty, readerPhysical, _newExtension, _newClassify⟩ := newReceipt
  have oldKey :
      (SourceRecursiveIntersectionEnvironment.enter beforeOld.native.machine.domains
        parent.key oldLeft oldRight oldFirst oldSecond).1.key =
      SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey [entry.identity]
        (pair entry.identity patternId) := sameKey.trans newKey
  obtain ⟨parentEmpty, oldLeftClosed, oldRightClosed, orderedIds⟩ :=
    SourceCurrentAllocatedNativeSourceEmptyEnterOperands.stored_dispatch_enter_closed_operands
      caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
      rootRequest rootEmpty sourceDecoded targetDecoded physical oldUsed beforeOld parent oldLeft oldRight
      oldFirst oldSecond entry.identity patternId oldNext oldPrefix oldKey
  have warmSpan : Trace (newUsed + 1) (.code (.node newRoot .pure)) oldSnapshot newControl reader :=
    newPrefix.trans newEntry
  have reached := SourceCurrentNativeEnterCommonOperand.checked_trace_extension warmSpan oldSnapshotPhysical
  have oldLeftAtReader : Available reader.native.machine.heap oldLeft :=
    reached.2.available oldLeft oldLeftAvailable
  have oldRightAtReader : Available reader.native.machine.heap oldRight :=
    reached.2.available oldRight oldRightAvailable
  have fullOperands : (oldLeft = universeValue ∧ oldRight = pattern) ∨
      (oldLeft = pattern ∧ oldRight = universeValue) := by
    rcases orderedIds with ⟨leftId, rightId⟩ | ⟨leftId, rightId⟩
    · exact Or.inl ⟨
        SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective reader.native.machine.heap
          readerPhysical.machine.1 oldLeft universeValue oldLeftAtReader universeAvailable
          oldLeftClosed universeClosed entry.identity leftId rfl,
        SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective reader.native.machine.heap
          readerPhysical.machine.1 oldRight pattern oldRightAtReader patternAvailable
          oldRightClosed patternClosed patternId rightId patternIdentity⟩
    · exact Or.inr ⟨
        SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective reader.native.machine.heap
          readerPhysical.machine.1 oldLeft pattern oldLeftAtReader patternAvailable
          oldLeftClosed patternClosed patternId leftId patternIdentity,
        SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective reader.native.machine.heap
          readerPhysical.machine.1 oldRight universeValue oldRightAtReader universeAvailable
          oldRightClosed universeClosed entry.identity rightId rfl⟩
  exact ⟨parentEmpty, fullOperands, oldLeftAtReader, oldRightAtReader, universeAvailable, patternAvailable⟩

end MicroCFTA.SourceCurrentAllocatedNativeSourceEnterFullOperands

#check MicroCFTA.SourceCurrentAllocatedNativeSourceEnterFullOperands.stored_dispatch_old_new_full_operands
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceEnterFullOperands.stored_dispatch_old_new_full_operands
