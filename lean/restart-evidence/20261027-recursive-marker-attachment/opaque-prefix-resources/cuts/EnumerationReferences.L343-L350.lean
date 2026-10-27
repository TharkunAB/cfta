/-- Every stored suspended reference avoids all expanded slots. -/
def PendingReferences (state : State Symbol Guard) : Prop :=
  ∀ held fragment, state.values[held]? = some (.enumerated fragment) → IncomingAvoid held state

/-- A stored pending payload inherits the state's avoidance of every expanded slot. -/
theorem pending_inputs (state : State Symbol Guard) (pending : PendingReferences state)
    (uv : Nat) (node : Option Nat) (scs : List Suspended) (stored : state.values[uv]? = some (.unenumerated node scs)) :
    InputsPending state scs := by
