import MicroCFTA.SourceCurrentIncomingSingletonCore
import MicroCFTA.SourceCurrentIncomingWaitingAppend
import MicroCFTA.SourceCurrentNativeSlotIndex

/-! Actual singleton cache returns derive all five fields at their literal reached caller. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSingletonCacheValid
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}

/-- Original facts derive full actual singleton cache validity for both stored handle options. -/
theorem singleton_cache_valid (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller reached : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs oldScs : List Suspended)
    (oldNode : Option Nat) (rooted : IsRoot before.core.representatives target)
    (stored : before.core.values[target]? = some (.unenumerated oldNode oldScs))
    (inside : target < before.core.counter) (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.core.counter)
    (savedQueries : SourceEndpointMemo.Memos) (read returned : Core) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query =
      ((.ok (some [.ok ((), returned)]), reached, savedQueries, read), some after) →
    CacheValid reached after := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro initial valid available closed fits room observed
  have validBefore := valid
  obtain ⟨roots, paths, _storage, _realized, counts, _flags⟩ := valid
  have incomingSame : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query =
      (.ok (some [.ok ((), returned)]), reached, savedQueries, read) := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run] using congrArg Prod.fst observed
  have rawObserved : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query).1 = .ok (some [.ok ((), returned)]) := by
    rw [incomingSame]
  have returnedFacts := SourceCurrentIncomingSingletonCore.singleton_core_effects symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before memos checkEmpty r n p h target incoming
    scs oldScs oldNode rooted stored inside bounded initial validBefore available closed fits room returned rawObserved
  dsimp only at returnedFacts
  rw [incomingSame] at returnedFacts
  dsimp only at returnedFacts
  obtain ⟨handle, returnedSame, returnedRepresentatives, _returnedCounter, returnedSlot,
    _returnedReferences, returnedStorage, returnedRealized⟩ := returnedFacts
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
  rw [incomingSame] at readFacts
  dsimp only at readFacts
  have coreSame := SourcePruningEnumerationIncomingCacheAdapter.singleton_core checkEmpty r n p h k
    caller reached before after target incoming scs memos.query savedQueries read returned observed
  let value : UVarValue Symbol := .unenumerated (some handle) (scs ++ oldScs)
  have returnedValues : returned.values = read.values.set target value := by rw [returnedSame]
  have afterValues : after.core.values = before.core.values.set target value := by
    rw [coreSame, returnedValues, readFacts.2.1]
  have cacheSome : (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query).2 = some after := congrArg Prod.snd observed
  have waitingSame := (SourceCurrentIncomingReadRoots.incoming_cache_observed symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h k caller before target incoming scs memos after roots paths cacheSome).1
  have afterCounts := SourceCurrentIncomingWaitingAppend.append_correct roots before.core.values target
    oldNode (some handle) scs oldScs before.waiting stored counts
  have actualCounts : EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting := by
    simpa only [afterValues, waitingSame, value] using afterCounts
  have frameFacts := SourceCurrentIncomingReadFrame.incoming_ok_frame_valid symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before memos checkEmpty r n p h target incoming
    scs inside initial validBefore available closed fits room
  change (let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core target incoming scs memos.query;
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧ CacheValid actual.2.1 (EnumerationExpandableIndex.frame actual.2.2.2 before)
    | .error _ => True) at frameFacts
  dsimp only at frameFacts
  rw [incomingSame] at frameFacts
  dsimp only at frameFacts
  obtain ⟨_next, _final, _post, _querySame, frameValid⟩ := frameFacts
  obtain ⟨_readRoots, _readPaths, _readStorage, _readRealized, _readCounts, readFlags⟩ := frameValid
  have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
      k target scs before read [.ok ((), returned)] = some after := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingSame] using congrArg Prod.snd observed
  have mapped : (SourcePruningEnumerationNativeIndex.write reached.checked.native.machine.heap k target value scs []
      (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned) = some after := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, returnedSlot, Option.bind_some, value] using adapted
  obtain ⟨written, writeObserved, afterSame⟩ := Option.map_eq_some_iff.mp mapped
  have storedRead : (EnumerationExpandableIndex.frame read before).core.values[target]? =
      some (.unenumerated oldNode oldScs) := by
    change read.values[target]? = some (.unenumerated oldNode oldScs)
    rw [readFacts.2.1]
    exact stored
  have writtenFlags := SourceCurrentNativeWriteFlags.write_flags reached.checked.native.machine.heap
    (EnumerationExpandableIndex.frame read before) written k target (.unenumerated oldNode oldScs)
    value scs [] readFlags storedRead writeObserved
  have writtenCore := SourceCurrentNativeSlotIndex.write_core reached.checked.native.machine.heap
    (EnumerationExpandableIndex.frame read before) written k target value scs [] writeObserved
  have writtenValues : written.core.values = returned.values := by
    simpa only [writtenCore, EnumerationExpandableIndex.frame] using returnedValues.symm
  have actualFlags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate reached.checked.native.machine.heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
    rw [← afterSame]
    intro slot
    change SourcePruningEnumerationNativeIndex.candidate reached.checked.native.machine.heap
      ((returned.values[slot]?).getD .eliminated) = some (written.expandable slot)
    rw [← writtenValues]
    exact writtenFlags slot
  refine ⟨roots, ?_, ?_, ?_, actualCounts, actualFlags⟩
  · simpa only [coreSame, returnedRepresentatives] using readFacts.1
  · simpa only [coreSame] using returnedStorage
  · simpa only [coreSame] using returnedRealized

end MicroCFTA.SourceCurrentIncomingSingletonCacheValid
