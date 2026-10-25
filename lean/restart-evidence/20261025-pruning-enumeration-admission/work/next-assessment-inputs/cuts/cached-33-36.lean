def allocate (graph : Graph Symbol Guard) (node : Option Nat) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  ⟨allocated node state.core,
    fun uv => if candidate graph (.unenumerated node []) && uv == state.core.counter then true else state.expandable uv,
    state.waiting⟩
