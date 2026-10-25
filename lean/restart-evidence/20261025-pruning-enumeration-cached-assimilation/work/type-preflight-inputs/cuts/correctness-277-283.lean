def assimilated (state : State Symbol Guard) (target source : Nat) (merged : UVarValue Symbol) : State Symbol Guard :=
  {state with
    values := (state.values.set target merged).set source .eliminated
    recursionAncestry := fun other => if other = target then
      (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
      else state.recursionAncestry other}

