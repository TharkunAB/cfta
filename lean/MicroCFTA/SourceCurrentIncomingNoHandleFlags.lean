import MicroCFTA.SourceCurrentIncomingReadStorage
import MicroCFTA.SourceCurrentNativeSlotIndex

/-! A stored slot with no node handle derives flags at its actual returned caller heap. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingNoHandleFlags
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem mapped_flags (heap : Heap) (before : Cached) (read returned : Core) (after : Cached)
    (fuel target : Nat) (old value : UVarValue Symbol) (scs : List Suspended)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (readValues : read.values = before.core.values) (stored : read.values[target]? = some old)
    (returnedValues : returned.values = read.values.set target value)
    (observed : (SourcePruningEnumerationNativeIndex.write heap fuel target value scs []
      (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned) = some after) :
    ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
  obtain ⟨written, writeObserved, same⟩ := Option.map_eq_some_iff.mp observed
  have readFlags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      (((EnumerationExpandableIndex.frame read before).core.values[slot]?).getD .eliminated) =
        some ((EnumerationExpandableIndex.frame read before).expandable slot) := by
    simpa only [EnumerationExpandableIndex.frame, readValues] using flags
  have writtenFlags := SourceCurrentNativeWriteFlags.write_flags heap
    (EnumerationExpandableIndex.frame read before) written fuel target old value scs [] readFlags stored writeObserved
  have writtenCore := SourceCurrentNativeSlotIndex.write_core heap
    (EnumerationExpandableIndex.frame read before) written fuel target value scs [] writeObserved
  have writtenValues : written.core.values = returned.values := by
    simpa only [writtenCore, EnumerationExpandableIndex.frame] using returnedValues.symm
  rw [← same]
  intro slot
  change SourcePruningEnumerationNativeIndex.candidate heap
    ((returned.values[slot]?).getD .eliminated) = some (written.expandable slot)
  rw [← writtenValues]
  exact writtenFlags slot

/-- Original flags derive actual cache flags for a stored slot that has no node handle. -/
theorem no_handle_singleton_flags (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h k : Nat) (caller reached : Caller width) (before after : Cached)
    (target : Nat) (incoming : Node) (scs oldScs : List Suspended) (memos : Memos)
    (savedQueries : SourceEndpointMemo.Memos) (read returned : Core)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (rooted : IsRoot before.core.representatives target) (storage : StorageValid before.core)
    (inside : target < before.core.counter)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (stored : before.core.values[target]? = some (.unenumerated none oldScs))
    (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.core.counter)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query =
      ((.ok (some [.ok ((), returned)]), reached, savedQueries, read), some after) →
    ∀ slot, SourcePruningEnumerationNativeIndex.candidate reached.checked.native.machine.heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro observed
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
  dsimp only at returnedFacts
  obtain ⟨callerSame, _querySame, handle, _encoded, returnedSame, _representatives, _counter,
    returnedSlot, _references, _roots, _storage, _realized⟩ := returnedFacts
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
  rw [incomingSame] at readFacts
  have readValues : read.values = before.core.values := readFacts.2.1
  have storedRead : read.values[target]? = some (.unenumerated none oldScs) := by
    rw [readValues]
    exact stored
  let value : UVarValue Symbol := .unenumerated (some handle) (scs ++ oldScs)
  have returnedValues : returned.values = read.values.set target value := by
    rw [returnedSame]
  have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
      k target scs before read [.ok ((), returned)] = some after := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingSame] using congrArg Prod.snd observed
  have mapped : (SourcePruningEnumerationNativeIndex.write reached.checked.native.machine.heap k target value scs []
      (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned) = some after := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, returnedSlot, Option.bind_some, value] using adapted
  rw [callerSame] at mapped
  have actualFlags := mapped_flags caller.checked.native.machine.heap before read returned after k target
    (.unenumerated none oldScs) value scs flags readValues storedRead returnedValues mapped
  simpa only [callerSame] using actualFlags

end MicroCFTA.SourceCurrentIncomingNoHandleFlags
