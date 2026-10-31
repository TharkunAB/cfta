import MicroCFTA.SourceCurrentCachedPrepareObserved
import MicroCFTA.SourcePruningEnumerationCachedPrepare

/-! Every actual prepared row derives its cache facts through the full input dispatch. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentCachedPrepareRowsObserved
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationObservation SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

/-- All input constructors retain fresh cache validity at the actual entry heap and fuel. -/
theorem prepare_child_row_valid (heap : InternedConstructorTemplates.State Symbol NativeGuard)
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
    (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard))
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild heap actualFuel scs value before = some rows)
    (member : (fragment, after) ∈ rows) :
    StorageValid after.core ∧ PendingRealized heap after.core ∧ Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
  cases value with
  | empty =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.some.injEq] at observed
      subst rows
      simp at member
  | reference => simp [SourcePruningEnumerationCachedPrepare.prepareChild] at observed
  | node entry edges depth free =>
      cases prepared : SourcePruningEnumerationCachedChild.prepareOrdinary heap actualFuel scs
          (.node entry edges depth free) before with
      | none => simp [SourcePruningEnumerationCachedPrepare.prepareChild, prepared] at observed
      | some result =>
          rcases result with ⟨actualFragment, actualCache⟩
          have rowsSame : [(actualFragment, actualCache)] = rows := by
            simpa only [SourcePruningEnumerationCachedPrepare.prepareChild, prepared, Option.map_some,
              Option.some.injEq] using observed
          have memberEq : (fragment, after) = (actualFragment, actualCache) := by
            simpa only [← rowsSame, List.mem_singleton] using member
          have cacheEq : after = actualCache := congrArg Prod.snd memberEq
          rw [cacheEq]
          exact SourceCurrentCachedPrepareObserved.prepare_ordinary_valid heap before actualCache scs
            (.node entry edges depth free) roots coherent available closed storage realized paths counts flags
            bounded actualFuel actualFragment prepared
  | union entry alternatives depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true => simp [SourcePruningEnumerationCachedPrepare.prepareChild, terminal] at observed
      | false =>
          obtain ⟨_, chosenFuel, producedRows, _, runAll, _, shape⟩ :=
            SourcePruningEnumerationCachedPrepare.complete heap before (.union entry alternatives depth free)
              scs roots coherent available closed storage realized paths counts flags bounded (fun _ => terminal)
          have actualRun : SourcePruningEnumerationCachedPrepare.prepareChild heap actualFuel scs
              (.union entry alternatives depth free) before = some producedRows := runAll 0
          have rowsEq : rows = producedRows := Option.some.inj (observed.symm.trans actualRun)
          subst rows
          rcases shape with ⟨impossible, _⟩ | ⟨produced, _, rowsSingleton, _, _, _, producedRoots,
            producedStorage, producedRealized, producedCounts, producedFlags, _⟩
          · cases impossible
          · have memberEq : (fragment, after) = (.hole before.core.counter, produced) := by
              simpa only [rowsSingleton, List.mem_singleton] using member
            have cacheEq : after = produced := congrArg Prod.snd memberEq
            rw [cacheEq]
            exact ⟨producedStorage, producedRealized, producedRoots, producedCounts, producedFlags⟩
  | mu entry body depth free =>
      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
      | true => simp [SourcePruningEnumerationCachedPrepare.prepareChild, terminal] at observed
      | false =>
          obtain ⟨_, chosenFuel, producedRows, _, runAll, _, shape⟩ :=
            SourcePruningEnumerationCachedPrepare.complete heap before (.mu entry body depth free)
              scs roots coherent available closed storage realized paths counts flags bounded (fun _ => terminal)
          have actualRun : SourcePruningEnumerationCachedPrepare.prepareChild heap actualFuel scs
              (.mu entry body depth free) before = some producedRows := runAll 0
          have rowsEq : rows = producedRows := Option.some.inj (observed.symm.trans actualRun)
          subst rows
          rcases shape with ⟨impossible, _⟩ | ⟨produced, _, rowsSingleton, _, _, _, producedRoots,
            producedStorage, producedRealized, producedCounts, producedFlags, _⟩
          · cases impossible
          · have memberEq : (fragment, after) = (.hole before.core.counter, produced) := by
              simpa only [rowsSingleton, List.mem_singleton] using member
            have cacheEq : after = produced := congrArg Prod.snd memberEq
            rw [cacheEq]
            exact ⟨producedStorage, producedRealized, producedRoots, producedCounts, producedFlags⟩

end MicroCFTA.SourceCurrentCachedPrepareRowsObserved
