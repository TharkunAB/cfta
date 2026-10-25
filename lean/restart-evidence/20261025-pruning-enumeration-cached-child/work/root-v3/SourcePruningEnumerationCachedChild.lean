import MicroCFTA.SourcePruningEnumerationNativeIndex
import MicroCFTA.SourcePruningEnumerationShallowChild

namespace MicroCFTA.SourcePruningEnumerationCachedChild
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Allocate the raw slot, update its native flag and inherit ancestry once. -/
def allocate
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node [])).map fun flag =>
    (before.core.counter,
      ⟨EnumerationState.allocated node before.core,
        fun slot => if flag then
          if slot = before.core.counter then true else before.expandable slot
          else before.expandable slot,
        before.waiting⟩)

/-- Read the old raw slot before the native full-constraint write. -/
def writeSlot
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : EnumerationState.UVarValue Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (before.core.values[target]?).bind fun old =>
    SourcePruningEnumerationNativeIndex.write heap fuel target value
      (references value) (references old) before

/-- Execute the ordinary nonterminal child branch with both native indexes. -/
def prepareOrdinary
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  match value with
  | .node _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).bind fun handle =>
          (allocate heap (some handle) before).bind fun allocation =>
            (writeSlot heap fuel allocation.1 (.unenumerated (some handle) scs) allocation.2).map
              fun after => (.hole allocation.1, after)
  | _ => none

/-- The decoded ordinary allocation derives the complete native flag scan. -/
theorem allocate_node_flags
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (handle : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol NativeGuard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (decoded : lookupNode heap handle = some (.node entry edges depth free))
    (aligned : before.core.counter = before.core.values.length)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ allocatedCached : EnumerationExpandableIndex.Cached Symbol EnumGuard,
      allocate heap (some handle) before = some (before.core.counter, allocatedCached) ∧
      allocatedCached.core = EnumerationState.allocated (some handle) before.core ∧
      allocatedCached.waiting = before.waiting ∧
      allocatedCached.expandable =
        (fun slot => if slot = before.core.counter then true else before.expandable slot) ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((allocatedCached.core.values[slot]?).getD .eliminated) =
          some (allocatedCached.expandable slot)) := by
  have candidateTrue : SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated (some handle) []) = some true := by
    simp only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
      MergedOrdinaryHeight.recursiveBoundary, Bool.false_and, Bool.not_false]
  refine ⟨⟨EnumerationState.allocated (some handle) before.core,
    fun slot => if slot = before.core.counter then true else before.expandable slot,
    before.waiting⟩, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [allocate, candidateTrue, Option.map_some, ↓reduceIte]
  · intro slot
    by_cases beforeSlot : slot < before.core.values.length
    · have different : slot ≠ before.core.counter := by
        rw [aligned]
        omega
      simpa only [EnumerationState.allocated, List.getElem?_append_left beforeSlot,
        ite_eq_right different] using flags slot
    · by_cases same : slot = before.core.counter
      · subst slot
        simpa only [EnumerationState.allocated_slot (some handle) before.core aligned,
          Option.getD_some, ↓reduceIte] using candidateTrue
      · have absent : before.core.values[slot]? = none := by
          exact List.getElem?_eq_none (by omega)
        have wholeAbsent : (EnumerationState.allocated (some handle) before.core).values[slot]? = none := by
          apply List.getElem?_eq_none
          simp only [EnumerationState.allocated, List.length_append, List.length_singleton]
          omega
        simpa only [wholeAbsent, absent, Option.getD_none, ite_eq_right same] using flags slot

/-- Derive the cached ordinary child sequence and its exact core execution. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol NativeGuard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap (.node entry edges depth free))
    (closed : free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
      (allocatedCached after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (fuel : Nat),
      encodeNode (.node entry edges depth free) = some handle ∧
      lookupNode heap handle = some (.node entry edges depth free) ∧
      SourcePruningEnumerationShallowChild.prepareChild scs (.node entry edges depth free) = some action ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      allocate heap (some handle) before = some (before.core.counter, allocatedCached) ∧
      allocatedCached.core = EnumerationState.allocated (some handle) before.core ∧
      allocatedCached.core.values[before.core.counter]? = some (.unenumerated (some handle) []) ∧
      StorageValid allocatedCached.core ∧ PendingRealized heap allocatedCached.core ∧
      EnumerationCanonicalWaiting.Correct roots allocatedCached.core.values allocatedCached.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((allocatedCached.core.values[slot]?).getD .eliminated) = some (allocatedCached.expandable slot)) ∧
      allocatedCached.waiting = before.waiting ∧
      (∀ (extra : Nat), writeSlot heap (fuel + extra) before.core.counter
        (.unenumerated (some handle) scs) allocatedCached = some after) ∧
      (∀ (extra : Nat), prepareOrdinary heap (fuel + extra) scs
        (.node entry edges depth free) before = some (.hole before.core.counter, after)) ∧
      after.core = {allocatedCached.core with values :=
              allocatedCached.core.values.set before.core.counter (.unenumerated (some handle) scs)} ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) scs) ∧
      after.core.counter = before.core.counter + 1 ∧ after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      after.expandable =
        (fun slot => if slot = before.core.counter then true else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots 1 scs before.waiting ∧
      FragmentBound after.core.counter (.hole before.core.counter) := by
  obtain ⟨handle, encoded, decoded, _emptyCase, nonemptyCase⟩ :=
    SourcePruningEnumerationShallowChild.prepareChild_complete heap before.core scs
      (.node entry edges depth free) coherent available closed realized storage.aligned nonterminal
  obtain ⟨action, coreAfter, prepared, _observed, afterShape, afterSlot, grows,
    alignedAfter, realizedAfter⟩ := nonemptyCase (by intro emptyValue; cases emptyValue)
  obtain ⟨allocatedHandle, allocatedEncoded, _allocation, baseStored, baseRealized⟩ :=
    SourcePruningEnumerationWrites.allocate_available_realized heap before.core
      (.node entry edges depth free) coherent available closed realized storage.aligned
  have allocatedHandleSame : allocatedHandle = handle := by
    exact Option.some.inj (allocatedEncoded.symm.trans encoded)
  subst allocatedHandle
  obtain ⟨allocatedCached, nativeAllocated, allocatedShape, waitingSame, flagShape, allocatedFlags⟩ :=
    allocate_node_flags heap before handle entry edges depth free decoded storage.aligned flags
  have allocatedStored : allocatedCached.core.values[before.core.counter]? =
      some (.unenumerated (some handle) []) := by
    simpa only [allocatedShape] using baseStored
  have allocatedStorage : StorageValid allocatedCached.core := by
    rw [allocatedShape]
    exact allocation_storage (some handle) before.core storage
  have allocatedRealized : PendingRealized heap allocatedCached.core := by
    simpa only [allocatedShape] using baseRealized
  have allocatedCounts : EnumerationCanonicalWaiting.Correct roots
      allocatedCached.core.values allocatedCached.waiting := by
    simpa only [allocatedShape, EnumerationState.allocated, waitingSame] using
      EnumerationCanonicalWaiting.allocate_correct roots before.core.values (some handle)
        before.waiting counts
  have allocatedPaths : Roots allocatedCached.core.representatives roots := by
    simpa only [allocatedShape, EnumerationState.allocated] using paths
  have inside : before.core.counter < allocatedCached.core.values.length := by
    exact (List.getElem?_eq_some_iff.mp allocatedStored).elim (fun bound _elementEquality => bound)
  have bound : SlotBound allocatedCached.core.counter (.unenumerated (some handle) scs) := by
    intro sc member
    rw [allocatedShape]
    exact Nat.lt_trans (bounded sc member) (Nat.lt_succ_self before.core.counter)
  obtain ⟨fuel, countRun⟩ := SourcePruningEnumerationNativeIndex.count_complete
    allocatedCached.core.representatives roots allocatedPaths scs
  let saved : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    ⟨{allocatedCached.core with values :=
      allocatedCached.core.values.set before.core.counter (.unenumerated (some handle) scs)},
      fun slot => if slot = before.core.counter then true else allocatedCached.expandable slot,
      EnumerationCanonicalWaiting.count roots 1 scs allocatedCached.waiting⟩
  have savedCore : saved.core = coreAfter := by
    simp only [saved, allocatedShape, afterShape]
  have savedStorage : StorageValid saved.core := by
    exact set_storage allocatedCached.core allocatedStorage before.core.counter
      (.unenumerated (some handle) scs) bound
  have savedCounts : EnumerationCanonicalWaiting.Correct roots saved.core.values saved.waiting := by
    simpa only [saved, EnumerationCanonicalWaiting.replace, references,
      EnumerationCanonicalWaiting.count, List.map_nil, EnumerationWaitingIndex.count,
      List.foldl_nil] using
      EnumerationCanonicalWaiting.replace_correct roots allocatedCached.core.values before.core.counter
        (.unenumerated (some handle) []) (.unenumerated (some handle) scs) allocatedStored
        allocatedCached.waiting allocatedCounts
  have savedFlags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((saved.core.values[slot]?).getD .eliminated) = some (saved.expandable slot) := by
    intro slot
    by_cases same : slot = before.core.counter
    · subst slot
      simp only [saved, List.getElem?_set_self inside, Option.getD_some,
        SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
        MergedOrdinaryHeight.recursiveBoundary, Bool.false_and, Bool.not_false, ↓reduceIte]
    · simpa only [saved, List.getElem?_set_ne (Ne.symm same), ite_eq_right same]
        using allocatedFlags slot
  have nativeRun : ∀ (extra : Nat), writeSlot heap (fuel + extra) before.core.counter
      (.unenumerated (some handle) scs) allocatedCached = some saved := by
    intro extra
    simp only [writeSlot, allocatedStored, Option.bind_some, references,
      SourcePruningEnumerationNativeIndex.write, SourcePruningEnumerationNativeIndex.candidate,
      decoded, Option.map_some, MergedOrdinaryHeight.recursiveBoundary,
      Bool.false_and, Bool.not_false,
      show SourcePruningEnumerationNativeIndex.count (fuel + extra)
        allocatedCached.core.representatives (-1) [] allocatedCached.waiting =
        some allocatedCached.waiting from rfl,
      countRun extra 1 allocatedCached.waiting, saved]
  have coreRaw : ExceptT.run (action before.core) =
      [.ok (.hole before.core.counter, saved.core)] := by
    simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
      Bool.false_eq_true, ↓reduceIte, encoded, Option.some.injEq] at prepared
    rw [← prepared]
    change [.ok (.hole before.core.counter,
      {EnumerationState.allocated (some handle) before.core with values :=
        (EnumerationState.allocated (some handle) before.core).values.set before.core.counter
          (.unenumerated (some handle) scs)})] = _
    rw [savedCore, afterShape]
  refine ⟨handle, action, allocatedCached, saved, fuel, encoded, decoded, prepared, coreRaw,
    nativeAllocated, allocatedShape, allocatedStored, allocatedStorage, allocatedRealized,
    allocatedCounts, allocatedFlags, waitingSame, nativeRun, ?_, rfl, ?_, ?_, ?_, ?_, ?_,
    savedStorage, ?_, savedCounts, savedFlags, ?_, ?_, ?_⟩
  · intro extra
    simp only [prepareOrdinary, nonterminal, Bool.false_eq_true, ↓reduceIte, encoded,
      Option.bind_some, nativeAllocated, nativeRun extra, Option.map_some]
  · simpa only [savedCore] using afterSlot
  · simpa only [savedCore] using grows
  · simpa only [savedCore] using alignedAfter
  · simp only [saved, allocatedShape, EnumerationState.allocated]
  · simpa only [saved, allocatedShape, EnumerationState.allocated] using paths
  · simpa only [savedCore] using realizedAfter
  · simp only [saved, flagShape]
    funext slot
    split <;> rfl
  · simp only [saved, waitingSame]
  · change before.core.counter < saved.core.counter
    rw [savedCore, grows]
    exact Nat.lt_succ_self _

end MicroCFTA.SourcePruningEnumerationCachedChild
