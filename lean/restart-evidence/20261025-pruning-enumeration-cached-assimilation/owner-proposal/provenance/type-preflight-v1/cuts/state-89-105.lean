def reject : EnumerateM Symbol Guard α := fun _ => []

/-- Choose each alternative with the same input state. -/
def choose (values : List α) : EnumerateM Symbol Guard α := fun state =>
  values.map fun value => .ok (value, state)

/-- Report an execution limit or source invariant failure. -/
def failure (error : Error) : EnumerateM Symbol Guard α := fun _ => [.error error]

/-- Retain a branch exactly when its Boolean guard is true. -/
def require (condition : Bool) : EnumerateM Symbol Guard Unit :=
  if condition then pure () else reject

/-- Write the supplied UVar, not its representative. -/
def setValue (uv : Nat) (value : UVarValue Symbol) : EnumerateM Symbol Guard Unit :=
  modify fun state => {state with values := state.values.set uv value}

