/-- An unblocked root has no stored incoming suspended reference. -/
theorem unblocked_incoming
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (uv : Nat) (root : IsRoot before.core.representatives uv)
    (unblocked : before.waiting uv = none) : EnumerationReferences.IncomingAvoid uv before.core := by
  intro value member
  cases value with
  | eliminated | enumerated _ => simp [references, EnumerationReferences.InputsAllowed]
  | unenumerated node scs =>
    obtain ⟨slot, stored⟩ := List.mem_iff_getElem?.mp member
    exact unblocked_avoids before roots paths counts uv root unblocked slot node scs stored

/-- Actual native selection derives the absence of incoming references at the same cache. -/
theorem incoming
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat) (safe : Safe before.core)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    EnumerationReferences.IncomingAvoid uv before.core :=
  unblocked_incoming before roots paths counts uv
    (ready heap before preference uv safe roots paths counts flags selected).root
    (offered before preference uv selected).2.2
