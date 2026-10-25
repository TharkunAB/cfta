import MicroCFTA.SourcePruningEnumerationReplacement

namespace MicroCFTA.SourcePruningEnumerationClear
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Clearing a recursive boundary removes its full bucket and derives the actual native indexes. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (after : EnumerationState.State Symbol EnumGuard)
    (target handle : Nat) (scs : List Suspended)
    (value : Value Symbol NativeGuard) (roots : Nat → Nat)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (realized : PendingRealized heap before.core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (written : Success (setValue target (.unenumerated (some handle) [])) before.core () after) :
    ∃ (fuel : Nat) (cached : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      (∀ extra, SourcePruningEnumerationNativeIndex.write heap (fuel + extra) target
        (.unenumerated (some handle) []) [] scs before = some cached) ∧
      cached.core = after ∧
      cached.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
      cached.expandable = (fun slot => if slot = target then false else before.expandable slot) ∧
      cached.expandable target = false ∧ EnumerationDriver.Ready target after ∧
      Roots after.representatives roots ∧ PendingRealized heap after ∧
      after.values[target]? = some (.unenumerated (some handle) []) ∧
      EnumerationCanonicalWaiting.Correct roots after.values cached.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.values[slot]?).getD .eliminated) = some (cached.expandable slot)) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before.core → EnumerationReferences.IncomingAvoid held after) := by
  have shape := (EnumerationDriver.modify_success _ before.core after).mp written
  have inside : target < before.core.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have afterSafe := (EnumerationDriver.setValue_safe target (.unenumerated (some handle) [])
    before.core after ready.safe ready.root (by intro impossible; cases impossible)
    (by simp [SlotBound]) written).1
  have afterReady : EnumerationDriver.Ready target after := by
    refine ⟨afterSafe, by simpa only [shape] using ready.inside, by simpa only [shape] using ready.root, ?_⟩
    intro node bucket read
    have emptyBucket : bucket = [] := by
      have parts : node = handle ∧ bucket = [] := by
        simpa only [shape, List.getElem?_set_self inside, Option.some.injEq,
          UVarValue.unenumerated.injEq, Option.some.injEq] using read.symm
      exact parts.2
    simp [emptyBucket, Avoids]
  have afterRealized : PendingRealized heap after := by
    intro slot node bucket read
    rw [shape] at read
    rcases List.mem_or_eq_of_mem_set (List.mem_of_getElem? read) with old | fresh
    · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
      exact realized oldSlot node bucket oldStored
    · obtain ⟨sameHandle, rfl⟩ := UVarValue.unenumerated.inj fresh
      cases Option.some.inj sameHandle
      obtain ⟨old, lookup, available, closed⟩ := realized target handle scs stored
      exact ⟨old, lookup, available, closed⟩
  obtain ⟨fuel, countRun⟩ := SourcePruningEnumerationNativeIndex.count_complete
    before.core.representatives roots paths scs
  let cached : EnumerationExpandableIndex.Cached Symbol EnumGuard := ⟨after,
    fun slot => if slot = target then false else before.expandable slot,
    EnumerationCanonicalWaiting.count roots (-1) scs before.waiting⟩
  refine ⟨fuel, cached, ?_, rfl, rfl, rfl, by simp [cached], afterReady,
    by simpa only [shape] using paths, afterRealized,
    by simpa only [shape] using List.getElem?_set_self inside, ?_, ?_,
    (fun history => EnumerationPendingReplacement.setValue_clear_pending target (some handle) scs
      before.core after stored history written),
    fun held incoming => EnumerationPendingReplacement.setValue_clear_incoming held target (some handle)
      before.core after incoming written⟩
  · intro extra
    simp only [SourcePruningEnumerationNativeIndex.write, SourcePruningEnumerationNativeIndex.candidate,
      decoded, Option.map_some, boundary, List.isEmpty_nil, Bool.and_self, Bool.not_true, Option.bind_some,
      countRun extra (-1) before.waiting, SourcePruningEnumerationNativeIndex.count]
    rw [← shape]
  · have counted := EnumerationCanonicalWaiting.replace_correct roots before.core.values target
      (.unenumerated (some handle) scs) (.unenumerated (some handle) []) stored before.waiting counts
    simpa only [shape, EnumerationCanonicalWaiting.replace, references, EnumerationCanonicalWaiting.count,
      List.map_nil, EnumerationWaitingIndex.count, List.foldl_nil] using counted
  · intro slot
    by_cases same : slot = target
    · subst slot
      simp only [shape, List.getElem?_set_self inside, Option.getD_some,
        SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some, boundary,
        List.isEmpty_nil, Bool.and_self, Bool.not_true, cached, ↓reduceIte]
    · simpa only [shape, List.getElem?_set_ne (Ne.symm same), cached, ite_eq_right same] using flags slot

end MicroCFTA.SourcePruningEnumerationClear
