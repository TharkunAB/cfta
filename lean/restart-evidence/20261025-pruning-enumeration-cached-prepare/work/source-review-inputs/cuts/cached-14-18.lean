/-- The source state adds an expandable set and a sparse waiting-count map. -/
structure Cached (Symbol Guard : Type) where
  core : State Symbol Guard
  expandable : Nat → Bool
  waiting : EnumerationWaitingIndex.Waiting
