import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
import MicroCFTA.SourceCurrentIncomingNoHandleFlags
import MicroCFTA.SourceCurrentIncomingWaitingAppend

/-! A stored slot with no node handle derives full actual cache validity on singleton success. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingNoHandleCacheValid
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
variable {width : Nat}

/-- Original entry validity derives actual fresh validity for the stored no-handle branch. -/
theorem no_handle_singleton_cache_valid (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h k : Nat) (caller reached : Caller width) (before after : Cached)
    (target : Nat) (incoming : Node) (scs oldScs : List Suspended) (memos : Memos)
    (savedQueries : SourceEndpointMemo.Memos) (read returned : Core)
    (initial : CacheValid caller before) (rooted : IsRoot before.core.representatives target)
    (inside : target < before.core.counter)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (stored : before.core.values[target]? = some (.unenumerated none oldScs))
    (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query =
      ((.ok (some [.ok ((), returned)]), reached, savedQueries, read), some after) →
    CacheValid reached after := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro observed
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := initial
  have incomingSame : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query =
      (.ok (some [.ok ((), returned)]), reached, savedQueries, read) := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run] using congrArg Prod.fst observed
  have rawObserved : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query).1 = .ok (some [.ok ((), returned)]) := by
    rw [incomingSame]
  have returnedFacts := SourceCurrentIncomingReadStorage.unstored_returned_core symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs oldScs memos roots paths rooted
    storage inside coherent realized available closed stored bounded returned rawObserved
  dsimp only at returnedFacts
  rw [incomingSame] at returnedFacts
  obtain ⟨_callerSame, _querySame, handle, _encoded, returnedSame, _representatives, _counter,
    _returnedSlot, _references, returnedRoots, returnedStorage, returnedRealized⟩ := returnedFacts
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
  rw [incomingSame] at readFacts
  have coreSame := SourcePruningEnumerationIncomingCacheAdapter.singleton_core checkEmpty r n p h k
    caller reached before after target incoming scs memos.query savedQueries read returned observed
  have afterValues : after.core.values =
      before.core.values.set target (.unenumerated (some handle) (scs ++ oldScs)) := by
    rw [coreSame, returnedSame]
    exact congrArg (fun values => values.set target (.unenumerated (some handle) (scs ++ oldScs))) readFacts.2.1
  have cacheSome : (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query).2 = some after := congrArg Prod.snd observed
  have waitingSame := (SourceCurrentIncomingReadRoots.incoming_cache_observed symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h k caller before target incoming scs memos after roots paths cacheSome).1
  have afterCounts := SourceCurrentIncomingWaitingAppend.append_correct roots before.core.values target
    none (some handle) scs oldScs before.waiting stored counts
  have actualCounts : EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting := by
    simpa only [afterValues, waitingSame] using afterCounts
  have actualFlags := SourceCurrentIncomingNoHandleFlags.no_handle_singleton_flags symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h k caller reached before after target incoming scs oldScs memos
    savedQueries read returned roots paths rooted storage inside coherent realized available closed stored bounded flags observed
  refine ⟨roots, ?_, ?_, ?_, actualCounts, actualFlags⟩
  · simpa only [coreSame] using returnedRoots
  · simpa only [coreSame] using returnedStorage
  · simpa only [coreSame] using returnedRealized

end MicroCFTA.SourceCurrentIncomingNoHandleCacheValid
