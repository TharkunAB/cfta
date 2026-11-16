import MicroCFTA.SourceCurrentAllocatedNativeSourceWarmEntry
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryDispatchOrigin
import MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEntry
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

theorem stored_dispatch_returned_or_authentic_entry_at
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
    (fuel wholeCount : Nat) (oldControl : Control (Value Symbol Guard)) (oldSnapshot : Checked width)
    (bounded : wholeCount ≤ fuel)
    (actual : Trace wholeCount (.code (.node rootRequest .pure)) caller.checked oldControl oldSnapshot)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (returned : oldSnapshot.native.nodes.cells handle = some ⟨request, .returned value⟩)
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
    caller.checked.native.nodes.cells handle = some ⟨request, .returned value⟩ ∨
      (AuthenticEntryAt rootRequest caller.checked wholeCount
        entry body depth ordinary pattern patternId request.domain ∧
       ∃ (queryUsed : Nat) (queryBefore : Checked width)
         (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
         queryUsed < wholeCount ∧ queryUsed < fuel ∧
         Trace queryUsed (.code (.node rootRequest .pure)) caller.checked
           (.code (.node request resume)) queryBefore)
 := by
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
        rootRequest caller.checked physical fuel finishUsed handle request value continuation beforeFinish
        (by omega) finishPrefix running
    have queryBeforeWhole : queryUsed < wholeCount := by omega
    have counts : queryUsed + (wholeCount - queryUsed) = wholeCount := by omega
    have wholeReindexed : Trace (queryUsed + (wholeCount - queryUsed))
        (.code (.node rootRequest .pure)) caller.checked oldControl oldSnapshot := by
      simpa only [counts] using actual
    have parts := SourceCurrentHereditaryNativePhysicalSplit.split issued.steps wholeReindexed
    have authenticated :=
      SourceCurrentAllocatedNativeSourceWarmEntry.stored_dispatch_issued_authentic_entry_at
        caller cached valid source target sourceHandle targetHandle sourceScs targetScs sourceStored targetStored
        rootRequest rootEmpty sourceDecoded targetDecoded physical queryUsed request resume queryBefore issued
        (wholeCount - queryUsed) oldControl oldSnapshot parts.2 entry body depth ordinary universeClosed
        pattern patternClosed patternId patternIdentity patternKind universeFirst newRoot newUsed beforeNew
        reader newNext newControl newPrefix newEntry matchingKey
    apply Or.inr
    refine ⟨?_, queryUsed, queryBefore, resume, queryBeforeWhole, queryFuel, issued⟩
    simpa only [counts] using authenticated

end MicroCFTA.SourceCurrentAllocatedNativeStoredDispatchReturnedWarmEntry
