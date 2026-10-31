import MicroCFTA.SourcePruningEnumerationNativeIndex

/-! Actual native-index writes preserve every decoded expandable flag. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentNativeWriteFlags
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

/-- Every actual successful write derives its flags from the original same-heap flags. -/
theorem write_flags (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (old value : UVarValue Symbol) (gained lost : List Suspended)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (stored : before.core.values[target]? = some old)
    (done : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before = some after) :
    ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot) := by
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
              intro slot
              by_cases same : slot = target
              · subst slot
                have bound := (List.getElem?_eq_some_iff.mp stored).1
                simpa only [List.getElem?_set_self bound, Option.getD_some, ↓reduceIte] using classified
              · simpa only [List.getElem?_set_ne (Ne.symm same), ite_eq_right same] using flags slot

end MicroCFTA.SourceCurrentNativeWriteFlags
