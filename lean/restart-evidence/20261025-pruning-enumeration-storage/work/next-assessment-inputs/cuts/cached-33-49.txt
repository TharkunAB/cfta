def allocate (graph : Graph Symbol Guard) (node : Option Nat) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  ⟨allocated node state.core,
    fun uv => if candidate graph (.unenumerated node []) && uv == state.core.counter then true else state.expandable uv,
    state.waiting⟩

/-- One raw-slot write removes old suspended counts before adding the new counts. -/
def write (graph : Graph Symbol Guard) (uv : Nat) (value : UVarValue Symbol) (state : Cached Symbol Guard) :
    Option (Cached Symbol Guard) := do
  let old ← state.core.values[uv]?
  pure ⟨{state.core with values := state.core.values.set uv value},
    fun other => if other = uv then candidate graph value else state.expandable other,
    EnumerationWaitingIndex.replace old value state.waiting⟩

/-- Other source effects update the original state without changing either index. -/
def frame (core : State Symbol Guard) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  {state with core := core}

