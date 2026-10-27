variable {EnumGuard NativeGuard : Type}

/-- The exact native candidate flag disables an isolated recursive boundary. -/
theorem IsolatedPending.disabled
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (held handle : Nat)
    (value : Value Symbol NativeGuard)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    before.expandable held = false := by
  simpa [SourcePruningEnumerationNativeIndex.candidate, isolated.stored, decoded, boundary]
    using (flags held).symm

/-- An actual pure selection cannot select the disabled isolated boundary. -/
theorem IsolatedPending.selected_ne
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) (held handle : Nat)
    (value : Value Symbol NativeGuard) (preference : List Nat → Option Nat) (uv : Nat)
    (isolated : IsolatedPending held handle before.core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) : uv ≠ held := by
  intro same
  subst uv
  have enabled := (SourcePruningEnumerationSelection.offered before preference held selected).2.1
  have disabled := isolated.disabled heap before held handle value decoded boundary flags
  rw [disabled] at enabled
  cases enabled
