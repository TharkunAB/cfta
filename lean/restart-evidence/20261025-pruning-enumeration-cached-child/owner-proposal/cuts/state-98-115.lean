/-- Retain a branch exactly when its Boolean guard is true. -/
def require (condition : Bool) : EnumerateM Symbol Guard Unit :=
  if condition then pure () else reject

/-- Write the supplied UVar, not its representative. -/
def setValue (uv : Nat) (value : UVarValue Symbol) : EnumerateM Symbol Guard Unit :=
  modify fun state => {state with values := state.values.set uv value}

/-- Read one raw slot. -/
def rawValue (uv : Nat) : EnumerateM Symbol Guard (UVarValue Symbol) := do
  match (← get).values[uv]? with
  | none => failure .invalidSlot
  | some value => pure value

/-- Find and path-compress a representative. -/
def representative (fuel uv : Nat) : EnumerateM Symbol Guard Nat := do
  let state ← get
  match UnionFind.findRoot fuel state.representatives uv with
