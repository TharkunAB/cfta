import MicroCFTA.SourcePruningEnumerationNativeIndex
import MicroCFTA.SourcePruningEnumerationObservation

namespace MicroCFTA.SourcePruningEnumerationFinalize
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance finalizeMonadList : Monad List := {
  pure := fun value => [value]
  bind := fun values continuation => values.flatMap continuation
}

/-- Clear expansion ancestry and store the fragment at the captured raw slot. -/
def finish (target : Nat) (fragment : Fragments.Fragment Symbol) :
    EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol) := do
  modify fun state => {state with expansionAncestry := []}
  let _old ← rawValue target
  setValue target (.enumerated fragment)
  pure fragment

/-- Use the current raw value to remove its waiting references after reset. -/
def run (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  let reset : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
    EnumerationExpandableIndex.frame {before.core with expansionAncestry := []} before
  (reset.core.values[target]?).bind fun old =>
    SourcePruningEnumerationNativeIndex.write heap fuel target (.enumerated fragment)
      [] (references old) reset

/-- Resetting ancestry and replacing a root by a bounded fragment retains safety. -/
theorem written_safe
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (target : Nat) (fragment : Fragments.Fragment Symbol)
    (safe : Safe before.core) (root : IsRoot before.core.representatives target)
    (bounded : FragmentBound before.core.counter fragment) :
    Safe {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  apply (EnumerationDriver.setValue_safe target (.enumerated fragment)
    {before.core with expansionAncestry := []} _
    (EnumerationDriver.ancestry_safe before.core [] safe) root (by simp) bounded ?_).1
  exact (EnumerationDriver.modify_success _ _ _).mpr rfl

/-- Derive finite finalization and the retained storage and index invariants. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (target : Nat) (fragment : Fragments.Fragment Symbol)
    (old : EnumerationState.UVarValue Symbol)
    (stored : before.core.values[target]? = some old)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (storage : StorageValid before.core)
    (bounded : FragmentBound before.core.counter fragment)
    (realized : PendingRealized heap before.core) :
    ∃ (fuel : Nat) (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      (∀ (extra : Nat), run heap (fuel + extra) target fragment before = some after) ∧
      ExceptT.run (finish (EnumGuard := EnumGuard) target fragment before.core) =
        [.ok (fragment, after.core)] ∧
      after.core = {before.core with
        values := before.core.values.set target (.enumerated fragment)
        expansionAncestry := []} ∧
      after.core.values[target]? = some (.enumerated fragment) ∧
      after.expandable = (fun (slot : Nat) => if slot = target then false else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots (-1) (references old) before.waiting ∧
      Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ (slot : Nat),
        SourcePruningEnumerationNativeIndex.candidate heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      (Safe before.core → IsRoot before.core.representatives target → Safe after.core) := by
  obtain ⟨fuel, countRun⟩ := SourcePruningEnumerationNativeIndex.count_complete
    before.core.representatives roots paths (references old)
  have inside : target < before.core.values.length := by
    exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)
  have writtenFlags : ∀ (slot : Nat),
    SourcePruningEnumerationNativeIndex.candidate heap
      (((before.core.values.set target (.enumerated fragment))[slot]?).getD .eliminated) =
      some (if slot = target then false else before.expandable slot) := by
    intro slot
    by_cases same : slot = target
    · subst slot
      simp only [List.getElem?_set_self inside, Option.getD_some,
        SourcePruningEnumerationNativeIndex.candidate, ↓reduceIte]
    · simpa only [List.getElem?_set_ne (Ne.symm same), ite_eq_right same] using flags slot
  have writtenStorage : StorageValid {before.core with
    values := before.core.values.set target (.enumerated fragment)
    expansionAncestry := []} := by
    exact ⟨(set_storage before.core storage target (.enumerated fragment) bounded).aligned,
      storage.total, storage.forest,
      (set_storage before.core storage target (.enumerated fragment) bounded).values,
      storage.guards⟩
  have writtenRealized : PendingRealized heap {before.core with
    values := before.core.values.set target (.enumerated fragment)
    expansionAncestry := []} := by
    intro slot node scs stored
    change (before.core.values.set target (.enumerated fragment))[slot]? =
      some (.unenumerated (some node) scs) at stored
    by_cases same : slot = target
    · subst slot
      simp only [List.getElem?_set_self inside] at stored
      cases stored
    · rw [List.getElem?_set_ne (Ne.symm same)] at stored
      exact realized slot node scs stored
  refine ⟨fuel, ⟨{before.core with
    values := before.core.values.set target (.enumerated fragment)
    expansionAncestry := []},
    fun slot => if slot = target then false else before.expandable slot,
    EnumerationCanonicalWaiting.count roots (-1) (references old) before.waiting⟩,
    ?_, ?_, rfl, List.getElem?_set_self inside, rfl, rfl, paths, ?_,
    writtenFlags, writtenStorage, writtenRealized,
    fun safe root => written_safe before target fragment safe root bounded⟩
  · intro extra
    simp only [run, EnumerationExpandableIndex.frame, stored, Option.bind_some,
      SourcePruningEnumerationNativeIndex.write, SourcePruningEnumerationNativeIndex.candidate,
      countRun extra (-1) before.waiting]
    rfl
  · dsimp [finish, rawValue, setValue, bind, pure, get, getThe, MonadStateOf.get,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.pure,
      StateT.get, StateT.modifyGet, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
      ExceptT.mk, ExceptT.run]
    simp only [List.flatMap_singleton, ExceptT.bindCont]
    rw [stored]
    rfl
  · exact EnumerationCanonicalWaiting.replace_correct roots before.core.values target old
      (.enumerated fragment) stored before.waiting counts

end MicroCFTA.SourcePruningEnumerationFinalize
