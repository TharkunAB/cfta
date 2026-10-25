def recordResidual (residual : Option Guard) (fragment : Fragment Symbol) : EnumerateM Symbol Guard Unit :=
  match residual with
  | none => pure ()
  | some guard => modify fun state => {state with obligations := (guard, fragment) :: state.obligations}

/-- Residual recording preserves safety when the guarded fragment refers only to allocated variables. -/
theorem recordResidual_safe (residual : Option Guard) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (safe : Safe before) (bounded : FragmentBound before.counter fragment)
    (success : Success (recordResidual residual fragment) before () after) : Safe after ∧ after.counter = before.counter := by
