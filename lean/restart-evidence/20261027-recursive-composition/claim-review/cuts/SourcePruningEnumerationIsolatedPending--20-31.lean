structure IsolatedPending (held handle : Nat) (state : State Symbol EnumGuard) : Prop where
  /-- The slot is a representative of its class. -/
  root : IsRoot state.representatives held
  /-- The actual pending payload retains its native handle. -/
  stored : state.values[held]? = some (.unenumerated (some handle) [])
  /-- Every stored suspended reference avoids this class. -/
  incoming : IncomingAvoid held state

/-- An isolated native pending slot contradicts full structural discharge. -/
theorem IsolatedPending.not_discharged
    (isolated : IsolatedPending held handle state) :
    ¬SourcePruningEnumerationRendering.Discharged state := by
