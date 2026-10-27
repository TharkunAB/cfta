/-- Native flags and canonical counts derive the caller's safe expansion precondition. -/
theorem ready
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat)
    (safe : Safe before.core)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    EnumerationDriver.Ready uv before.core := by
  obtain ⟨inside, flag, unblocked⟩ := offered before preference uv selected
  have insideValues : uv < before.core.values.length := by
    rw [← safe.1.aligned]
    exact inside
  have stored : before.core.values[uv]? = some before.core.values[uv] :=
    List.getElem?_eq_getElem insideValues
  have nativeFlag : SourcePruningEnumerationNativeIndex.candidate heap before.core.values[uv] =
      some true := by
    simpa only [stored, Option.getD_some, flag] using flags uv
  have live : before.core.values[uv] ≠ .eliminated := by
    intro eliminated
    simp only [eliminated, SourcePruningEnumerationNativeIndex.candidate] at nativeFlag
    cases nativeFlag
  have root : IsRoot before.core.representatives uv := (safe.2 uv _ stored).mp live
  exact ⟨safe, inside, root, fun node scs read =>
    unblocked_avoids before roots paths counts uv root unblocked uv (some node) scs read⟩
