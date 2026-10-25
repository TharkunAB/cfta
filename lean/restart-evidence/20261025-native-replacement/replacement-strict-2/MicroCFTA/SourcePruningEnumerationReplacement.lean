import MicroCFTA.SourcePruningEnumerationNativeGrowth
import MicroCFTA.EnumerationPendingReplacement

namespace MicroCFTA.SourcePruningEnumerationReplacement
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Removing and adding the same bucket retains a canonical sparse count table. -/
theorem count_cancel (roots : Nat → Nat) (scs : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (canonical : EnumerationWaitingIndex.Canonical waiting) :
    EnumerationCanonicalWaiting.count roots 1 scs
      (EnumerationCanonicalWaiting.count roots (-1) scs waiting) = waiting := by
  unfold EnumerationCanonicalWaiting.count
  let mapped := scs.map (fun sc => {sc with var := roots sc.var})
  have sparse := EnumerationWaitingIndex.count_canonical 1 mapped
    (EnumerationWaitingIndex.count (-1) mapped waiting)
    (EnumerationWaitingIndex.count_canonical (-1) mapped waiting canonical)
  funext key
  rw [sparse key, canonical key]
  congr 1
  simp only [EnumerationWaitingIndex.count_read, Int.one_mul, Int.neg_one_mul]
  omega

/-- The actual pending-handle replacement derives both native indexes at its written cache. -/
theorem complete
    (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (after : EnumerationState.State Symbol EnumGuard)
    (target oldHandle newHandle : Nat) (scs : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard) (roots : Nat → Nat)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (stored : before.core.values[target]? = some (.unenumerated (some oldHandle) scs))
    (realized : PendingRealized heap before.core)
    (decoded : lookupNode nextHeap newHandle = some value)
    (available : Available nextHeap value) (closed : value.free = [])
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (written : Success (setValue target (.unenumerated (some newHandle) scs)) before.core () after) :
    ∃ (fuel : Nat) (cached : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      (∀ extra, SourcePruningEnumerationNativeIndex.write nextHeap (fuel + extra) target
        (.unenumerated (some newHandle) scs) scs scs before = some cached) ∧
      cached.core = after ∧ cached.waiting = before.waiting ∧
      cached.expandable = (fun slot => if slot = target then
        !(MergedOrdinaryHeight.recursiveBoundary value && scs.isEmpty) else before.expandable slot) ∧
      Safe after ∧ Roots after.representatives roots ∧ PendingRealized nextHeap after ∧
      after.values[target]? = some (.unenumerated (some newHandle) scs) ∧
      EnumerationCanonicalWaiting.Correct roots after.values cached.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate nextHeap
        ((after.values[slot]?).getD .eliminated) = some (cached.expandable slot)) ∧
      (EnumerationDriver.Ready target before.core → EnumerationDriver.Ready target after) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before.core → EnumerationReferences.IncomingAvoid held after) := by
  have shape := (EnumerationDriver.modify_success _ before.core after).mp written
  have inside : target < before.core.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have root : IsRoot before.core.representatives target :=
    (safe.2 target _ stored).mp (by intro impossible; cases impossible)
  have bounded : SlotBound before.core.counter (.unenumerated (some newHandle) scs) := by
    have oldBound := safe.1.values _ (List.mem_of_getElem? stored)
    exact oldBound
  have afterSafe := (EnumerationDriver.setValue_safe target (.unenumerated (some newHandle) scs)
    before.core after safe root (by intro impossible; cases impossible) bounded written).1
  have grownFlags := SourcePruningEnumerationNativeGrowth.flags heap nextHeap kept before flags
  have grownRealized := realized_preserved heap nextHeap before.core before.core realized (.refl _) kept
  have afterRealized : PendingRealized nextHeap after := by
    intro slot handle bucket read
    rw [shape] at read
    rcases List.mem_or_eq_of_mem_set (List.mem_of_getElem? read) with old | fresh
    · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
      exact grownRealized oldSlot handle bucket oldStored
    · obtain ⟨rfl, rfl⟩ := UVarValue.unenumerated.inj fresh
      exact ⟨value, decoded, available, closed⟩
  obtain ⟨fuel, countRun⟩ := SourcePruningEnumerationNativeIndex.count_complete
    before.core.representatives roots paths scs
  have cancel := count_cancel roots scs before.waiting (EnumerationWaitingIndex.Correct.facts counts).1
  let cached : EnumerationExpandableIndex.Cached Symbol EnumGuard := ⟨after,
    fun slot => if slot = target then
      !(MergedOrdinaryHeight.recursiveBoundary value && scs.isEmpty) else before.expandable slot,
    before.waiting⟩
  refine ⟨fuel, cached, ?_, rfl, rfl, rfl, afterSafe, ?_, afterRealized,
    by simpa only [shape] using List.getElem?_set_self inside,
    ?_, ?_, ?_, EnumerationPendingReplacement.setValue_pending target (some oldHandle) (some newHandle)
      scs before.core after stored · written,
    fun held incoming => EnumerationPendingReplacement.setValue_incoming held target (some oldHandle)
      (some newHandle) scs before.core after stored incoming written⟩
  · intro extra
    simp only [SourcePruningEnumerationNativeIndex.write, SourcePruningEnumerationNativeIndex.candidate,
      decoded, Option.map_some, Option.bind_some, countRun extra (-1) before.waiting,
      countRun extra 1 (EnumerationCanonicalWaiting.count roots (-1) scs before.waiting), cancel]
    rw [← shape]
  · simpa only [shape] using paths
  · have counted := SourcePruningEnumerationTerminal.gained_correct before.core.values target
      (some oldHandle) (some newHandle) [] scs roots before.waiting stored counts
    simpa only [shape, List.nil_append, EnumerationCanonicalWaiting.count, List.map_nil,
      EnumerationWaitingIndex.count, List.foldl_nil] using counted
  · intro slot
    by_cases same : slot = target
    · subst slot
      simp only [shape, List.getElem?_set_self inside, Option.getD_some,
        SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some, cached, ↓reduceIte]
    · simpa only [shape, List.getElem?_set_ne (Ne.symm same), cached, ite_eq_right same] using grownFlags slot
  · intro ready
    refine ⟨afterSafe, by simpa only [shape] using ready.inside, by simpa only [shape] using root, ?_⟩
    intro handle bucket read
    have same : handle = newHandle ∧ bucket = scs := by
      simpa only [shape, List.getElem?_set_self inside, Option.some.injEq,
        UVarValue.unenumerated.injEq, Option.some.injEq] using read.symm
    simpa only [same.2, shape] using ready.avoids oldHandle scs stored

end MicroCFTA.SourcePruningEnumerationReplacement
