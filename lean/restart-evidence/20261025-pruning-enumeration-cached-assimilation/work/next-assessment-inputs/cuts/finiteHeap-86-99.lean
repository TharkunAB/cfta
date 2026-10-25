/-- Physical input checks are required only along the actual reached control path. -/
noncomputable def InputsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → State width → Prop
  | 0, control, state => Inputs control state
  | fuel + 1, control, state =>
      Inputs control state ∧ match step control state with
      | .yielded next after => InputsThrough fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- Every finite actual native execution retains its ready heap and both physical histories. -/
theorem execute_keeps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : State width) (ready : Ready state.native.machine.heap)
    (inputs : InputsThrough fuel control state) :
    Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap := by
