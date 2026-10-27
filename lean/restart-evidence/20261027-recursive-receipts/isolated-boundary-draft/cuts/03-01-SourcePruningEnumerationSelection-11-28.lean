theorem offered
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (preference : List Nat → Option Nat) (uv : Nat)
    (selected : EnumerationPureSelection.next preference before = .expand uv) :
    uv < before.core.counter ∧ before.expandable uv = true ∧ before.waiting uv = none := by
  dsimp only [EnumerationPureSelection.next, EnumerationPureSelection.find] at selected
  split at selected
  · cases selected
  · have member := pickNext_safe preference _ uv selected
    obtain ⟨candidate, unblocked⟩ := List.mem_filter.mp member
    obtain ⟨inside, flag⟩ := List.mem_filter.mp candidate
    exact ⟨List.mem_range.mp inside, flag, Option.isNone_iff_eq_none.mp unblocked⟩

/-- Exact waiting counts separate an unblocked root from every stored reference. -/
theorem unblocked_avoids
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
