  deriving DecidableEq, Repr

/-- State and errors are local to each nondeterministic alternative. -/
abbrev EnumerateM (Symbol Guard : Type) := StateT (State Symbol Guard) (ExceptT Error List)

/-- Reject one branch, as the list monad does. -/
def reject : EnumerateM Symbol Guard α := fun _ => []

/-- Choose each alternative with the same input state. -/
def choose (values : List α) : EnumerateM Symbol Guard α := fun state =>
  values.map fun value => .ok (value, state)

/-- Report an execution limit or source invariant failure. -/
def failure (error : Error) : EnumerateM Symbol Guard α := fun _ => [.error error]
