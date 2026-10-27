/-- Pure selection returns an allocated candidate with no waiting entry. -/
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
