structure Cached (Symbol Guard : Type) where
  /-- The complete six-field enumeration core. -/
  core : EnumerationFlatState.State Symbol Guard
  /-- The maintained expandable flag at each raw slot. -/
  expandable : Nat → Bool
  /-- The sparse waiting count at each variable identifier. -/
  waiting : EnumerationWaitingIndex.Waiting

/-- Correspondence keeps both complete indexes and relates the complete core. -/
structure Related (flat : Cached Symbol Guard)
    (earlier : EnumerationExpandableIndex.Cached Symbol Guard) : Prop where
  /-- All non-forest fields agree and the forests have equal roots and sizes. -/
  core : EnumerationFlatState.Related flat.core earlier.core
  /-- The complete expandable functions agree. -/
  expandable : flat.expandable = earlier.expandable
  /-- The complete sparse waiting functions agree. -/
  waiting : flat.waiting = earlier.waiting

/-- Replace the core without changing the cached indexes. -/
