import MicroCFTA.SourceCurrentNativeWriteFlags
import MicroCFTA.SourceCurrentNativeCountObserved
import MicroCFTA.SourcePruningEnumerationCachedChild

/-! Actual cached slot writes retain roots and derive both native indexes. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentNativeSlotIndex
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

/-- An actual native write changes only the stored value in the enumeration core. -/
theorem write_core (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (done : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before = some after) :
    after.core = {before.core with values := before.core.values.set target value} := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [SourcePruningEnumerationNativeIndex.write, classified] at done
  | some flag =>
      cases removedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives (-1) lost before.waiting with
      | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq] at done
      | some removed =>
          cases savedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives 1 gained removed with
          | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
          | some saved =>
              simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
              subst after
              rfl

/-- Exact old and new slot references derive waiting correctness at every successful fuel. -/
theorem write_waiting_correct (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (old value : UVarValue Symbol) (roots : Nat → Nat)
    (paths : Roots before.core.representatives roots)
    (waiting : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (stored : before.core.values[target]? = some old)
    (done : SourcePruningEnumerationNativeIndex.write heap fuel target value
      (references value) (references old) before = some after) :
    EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting := by
  have coreSame := write_core heap before after fuel target value (references value) (references old) done
  have waitingSame := SourceCurrentNativeCountObserved.write_waiting heap before after fuel target value
    (references value) (references old) roots paths done
  have correct := EnumerationCanonicalWaiting.replace_correct roots before.core.values target old value
    stored before.waiting waiting
  simpa only [coreSame, waitingSame, EnumerationCanonicalWaiting.replace] using correct

/-- The literal cached slot adapter derives roots and indexes from its original packet components. -/
theorem write_slot_index (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (roots : Nat → Nat)
    (paths : Roots before.core.representatives roots)
    (waiting : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (done : SourcePruningEnumerationCachedChild.writeSlot heap fuel target value before = some after) :
    after.core.counter = before.core.counter ∧ Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
  cases oldRead : before.core.values[target]? with
  | none => simp [SourcePruningEnumerationCachedChild.writeSlot, oldRead] at done
  | some old =>
      have observed : SourcePruningEnumerationNativeIndex.write heap fuel target value
          (references value) (references old) before = some after := by
        simpa only [SourcePruningEnumerationCachedChild.writeSlot, oldRead, Option.bind_some] using done
      have coreSame := write_core heap before after fuel target value (references value) (references old) observed
      refine ⟨?_, ?_, write_waiting_correct heap before after fuel target old value roots paths waiting oldRead observed,
        SourceCurrentNativeWriteFlags.write_flags heap before after fuel target old value
          (references value) (references old) flags oldRead observed⟩
      · simp only [coreSame]
      · simpa only [coreSame] using paths

end MicroCFTA.SourceCurrentNativeSlotIndex
