theorem allocated_isolated (before : State Symbol EnumGuard) (handle : Nat) (safe : Safe before) :
    IsolatedPending before.counter handle (allocated (some handle) before) := by
