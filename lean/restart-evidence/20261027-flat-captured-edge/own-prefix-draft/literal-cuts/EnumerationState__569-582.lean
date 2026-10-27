def allocated (node : Option Nat) (state : State Symbol Guard) : State Symbol Guard :=
  {state with
    counter := state.counter + 1
    values := state.values ++ [UVarValue.unenumerated node []]
    recursionAncestry := (fun other =>
      if other = state.counter then (state.expansionAncestry ++ state.recursionAncestry state.counter).eraseDups
      else state.recursionAncestry other)}

/-- Allocation has exactly one result and retains all old value slots. -/
theorem allocate_exact (node : Option Nat) (state : State Symbol Guard) :
    allocate node state = [.ok (state.counter, allocated node state)] := rfl

/-- The fresh-name supply remains equal to the slot count after allocation. -/
theorem allocated_supply (node : Option Nat) (state : State Symbol Guard)
