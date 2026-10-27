
/-- Allocate one raw slot and retain the core ancestry update. -/
def allocate (node : Option Nat) : Action Symbol Guard Nat := do
  let state ← get
  let uv := state.counter
  set {state with counter := uv + 1, values := state.values ++ [UVarValue.unenumerated node []]}
  inheritAncestry uv
  pure uv

end MicroCFTA.EnumerationFlatState
