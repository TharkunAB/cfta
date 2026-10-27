structure Related (flat : Cached Symbol Guard)
    (earlier : EnumerationExpandableIndex.Cached Symbol Guard) : Prop where
  /-- All non-forest fields agree and the forests have equal roots and sizes. -/
  core : EnumerationFlatState.Related flat.core earlier.core
  /-- The complete expandable functions agree. -/
  expandable : flat.expandable = earlier.expandable
  /-- The complete sparse waiting functions agree. -/
  waiting : flat.waiting = earlier.waiting
