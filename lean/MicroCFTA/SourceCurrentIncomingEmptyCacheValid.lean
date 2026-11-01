import MicroCFTA.SourceCurrentIncomingSingletonCacheValid
import MicroCFTA.SourceCurrentIncomingEmptyAvailable

/-! Literal empty raw returns derive full validity of the actual optional cache. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingEmptyCacheValid
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

/-- Original facts derive all five fields for the literal empty-row cache branch. -/
theorem empty_cache_valid (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller reached : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs oldScs : List Suspended)
    (oldNode : Option Nat)
    (stored : before.core.values[target]? = some (.unenumerated oldNode oldScs))
    (inside : target < before.core.counter) (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.core.counter)
    (savedQueries : SourceEndpointMemo.Memos) (read : Core) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query = ((.ok (some []), reached, savedQueries, read), some after) →
    CacheValid reached after := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro initial valid available closed fits room observed
  have validBefore := valid
  obtain ⟨roots, paths, storage, _realized, counts, _flags⟩ := valid
  have incomingSame : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query = (.ok (some []), reached, savedQueries, read) := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run] using congrArg Prod.fst observed
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
  rw [incomingSame] at readFacts
  dsimp only at readFacts
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
  obtain ⟨_next, _final, post, _querySame, frameValid⟩ := frameFacts
  obtain ⟨_readRoots, _readPaths, readStorage, readRealized, _readCounts, readFlags⟩ := frameValid
  have readInside : target < read.values.length := by
    rw [readFacts.2.1, ← storage.aligned]
    exact inside
  have readBound : ∀ sc ∈ scs ++ oldScs, sc.var < read.counter := by
    rw [readFacts.2.2]
    exact bounded
  have emptyAvailable := SourceCurrentIncomingEmptyAvailable.empty_available reached
  have coherent := post.context.ready.good.heap.semantic.1.normal.facts.coherent
  obtain ⟨produced, _prefix, _finish, producedSame, _producedSlot, producedStorage, producedRealized⟩ :=
    SourcePruningEnumerationIncomingNode.finish_complete reached.checked.native.machine.heap
      read (.empty : Node) target 0 scs oldScs coherent emptyAvailable rfl rfl readRealized
      readStorage readInside readBound
  let value : UVarValue Symbol := .unenumerated (some 0) (scs ++ oldScs)
  have storedRead : read.values[target]? = some (.unenumerated oldNode oldScs) := by
    rw [readFacts.2.1]
    exact stored
  have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
      k target scs before read [] = some after := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingSame] using congrArg Prod.snd observed
  have mapped : (SourcePruningEnumerationNativeIndex.write reached.checked.native.machine.heap k target value scs []
      (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame produced) = some after := by
    rw [producedSame]
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, storedRead, value] using adapted
  obtain ⟨written, writeObserved, afterSame⟩ := Option.map_eq_some_iff.mp mapped
  have coreSame : after.core = produced := by
    rw [← afterSame]
    rfl
  have producedValues : produced.values = read.values.set target value := by rw [producedSame]
  have afterValues : after.core.values = before.core.values.set target value := by
    rw [coreSame, producedValues, readFacts.2.1]
  have cacheSome : (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query).2 = some after := congrArg Prod.snd observed
  have waitingSame := (SourceCurrentIncomingReadRoots.incoming_cache_observed symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h k caller before target incoming scs memos after roots paths cacheSome).1
  have afterCounts := SourceCurrentIncomingWaitingAppend.append_correct roots before.core.values target
    oldNode (some 0) scs oldScs before.waiting stored counts
  have actualCounts : EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting := by
    simpa only [afterValues, waitingSame, value] using afterCounts
  have storedFrame : (EnumerationExpandableIndex.frame read before).core.values[target]? =
      some (.unenumerated oldNode oldScs) := storedRead
  have writtenFlags := SourceCurrentNativeWriteFlags.write_flags reached.checked.native.machine.heap
    (EnumerationExpandableIndex.frame read before) written k target (.unenumerated oldNode oldScs)
    value scs [] readFlags storedFrame writeObserved
  have writtenCore := SourceCurrentNativeSlotIndex.write_core reached.checked.native.machine.heap
    (EnumerationExpandableIndex.frame read before) written k target value scs [] writeObserved
  have writtenValues : written.core.values = produced.values := by
    simpa only [writtenCore, EnumerationExpandableIndex.frame] using producedValues.symm
  have actualFlags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate reached.checked.native.machine.heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
    rw [← afterSame]
    intro slot
    change SourcePruningEnumerationNativeIndex.candidate reached.checked.native.machine.heap
      ((produced.values[slot]?).getD .eliminated) = some (written.expandable slot)
    rw [← writtenValues]
    exact writtenFlags slot
  refine ⟨roots, ?_, ?_, ?_, actualCounts, actualFlags⟩
  · simpa only [coreSame, producedSame] using readFacts.1
  · simpa only [coreSame] using producedStorage
  · simpa only [coreSame] using producedRealized

end MicroCFTA.SourceCurrentIncomingEmptyCacheValid
