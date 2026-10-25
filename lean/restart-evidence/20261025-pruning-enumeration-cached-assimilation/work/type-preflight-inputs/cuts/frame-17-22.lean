  expandable : Nat → Bool
  waiting : EnumerationWaitingIndex.Waiting

/-- Both cached indexes agree with the complete value-slot scan. -/
structure Correct (graph : Graph Symbol Guard) (state : Cached Symbol Guard) : Prop where
  aligned : state.core.counter = state.core.values.length
