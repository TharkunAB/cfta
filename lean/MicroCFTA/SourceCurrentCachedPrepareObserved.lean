import MicroCFTA.SourceCurrentNativeCountObserved
import MicroCFTA.SourcePruningEnumerationCachedChild

/-! Successful cached preparation derives its cache facts at the actual supplied fuel. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentCachedPrepareObserved
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationObservation SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

private theorem write_exact (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots) (flag : Bool)
    (classified : SourcePruningEnumerationNativeIndex.candidate heap value = some flag)
    (done : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before = some after) :
    after = ⟨{before.core with values := before.core.values.set target value},
      (fun slot => if slot = target then flag else before.expandable slot),
      EnumerationCanonicalWaiting.count roots 1 gained
        (EnumerationCanonicalWaiting.count roots (-1) lost before.waiting)⟩ := by
  have waitingSame := SourceCurrentNativeCountObserved.write_waiting heap before after fuel target value
    gained lost roots paths done
  cases removedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives (-1) lost before.waiting with
  | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq] at done
  | some removed =>
      cases savedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives 1 gained removed with
      | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
      | some saved =>
          simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
          subst after
          change saved = _ at waitingSame
          simp only [waitingSame]

/-- Two actual successful native writes agree at any fuels on the same original rooted cache. -/
theorem write_some_unique (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before first second : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (firstFuel secondFuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (firstDone : SourcePruningEnumerationNativeIndex.write heap firstFuel target value gained lost before = some first)
    (secondDone : SourcePruningEnumerationNativeIndex.write heap secondFuel target value gained lost before = some second) :
    first = second := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [SourcePruningEnumerationNativeIndex.write, classified] at firstDone
  | some flag =>
      exact (write_exact heap before first firstFuel target value gained lost roots paths flag classified firstDone).trans
        (write_exact heap before second secondFuel target value gained lost roots paths flag classified secondDone).symm

/-- The literal slot adapter has one successful cache at all supplied fuels. -/
theorem write_slot_some_unique (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before first second : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (firstFuel secondFuel target : Nat) (value : UVarValue Symbol)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (firstDone : SourcePruningEnumerationCachedChild.writeSlot heap firstFuel target value before = some first)
    (secondDone : SourcePruningEnumerationCachedChild.writeSlot heap secondFuel target value before = some second) :
    first = second := by
  cases oldRead : before.core.values[target]? with
  | none => simp [SourcePruningEnumerationCachedChild.writeSlot, oldRead] at firstDone
  | some old =>
      have firstWrite : SourcePruningEnumerationNativeIndex.write heap firstFuel target value
          (references value) (references old) before = some first := by
        simpa only [SourcePruningEnumerationCachedChild.writeSlot, oldRead, Option.bind_some] using firstDone
      have secondWrite : SourcePruningEnumerationNativeIndex.write heap secondFuel target value
          (references value) (references old) before = some second := by
        simpa only [SourcePruningEnumerationCachedChild.writeSlot, oldRead, Option.bind_some] using secondDone
      exact write_some_unique heap before first second firstFuel secondFuel target value
        (references value) (references old) roots paths firstWrite secondWrite

/-- Actual preparation derives fresh cache validity from its original packet and input facts. -/
theorem prepare_ordinary_valid (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (roots : Nat → Nat) (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (actualFuel : Nat) (fragment : Fragments.Fragment Symbol)
    (observed : SourcePruningEnumerationCachedChild.prepareOrdinary heap actualFuel scs value before =
      some (fragment, after)) :
    StorageValid after.core ∧ PendingRealized heap after.core ∧ Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
  cases value with
  | empty | reference | union | mu =>
      simp [SourcePruningEnumerationCachedChild.prepareOrdinary] at observed
  | node entry edges depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true => simp [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal] at observed
      | false =>
          obtain ⟨handle, _, allocated, produced, chosenFuel, encoded, _, _, _, allocatedRun, allocatedCore,
            _, _, _, _, _, _, writeAll, _, _, _, _, _, _, producedRoots, producedStorage,
            producedRealized, producedCounts, producedFlags, _⟩ :=
            SourcePruningEnumerationCachedChild.complete heap before entry edges depth free scs roots
              coherent available closed storage realized paths counts flags bounded terminal
          have allocatedPaths : Roots allocated.core.representatives roots := by
            simpa only [allocatedCore, EnumerationState.allocated] using paths
          cases actualWrite : SourcePruningEnumerationCachedChild.writeSlot heap actualFuel before.core.counter
              (.unenumerated (some handle) scs) allocated with
          | none =>
              simp [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, encoded, allocatedRun,
                actualWrite] at observed
          | some actualCache =>
              have resultEq : (Fragments.Fragment.hole before.core.counter, actualCache) = (fragment, after) := by
                simpa only [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, Bool.false_eq_true,
                  ↓reduceIte, encoded, Option.bind_some, allocatedRun, actualWrite, Option.map_some,
                  Option.some.injEq] using observed
              have cacheEq : actualCache = after := congrArg Prod.snd resultEq
              have actualSame := write_slot_some_unique heap allocated actualCache produced actualFuel chosenFuel
                before.core.counter (.unenumerated (some handle) scs) roots allocatedPaths actualWrite (writeAll 0)
              have afterSame := cacheEq.symm.trans actualSame
              rw [afterSame]
              exact ⟨producedStorage, producedRealized, producedRoots, producedCounts, producedFlags⟩

end MicroCFTA.SourceCurrentCachedPrepareObserved
