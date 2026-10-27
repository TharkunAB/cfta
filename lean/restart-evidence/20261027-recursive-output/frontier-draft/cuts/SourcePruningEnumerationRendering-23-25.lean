def Discharged (state : EnumerationState.State Symbol EnumGuard) : Prop :=
  ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
    state.values[uv]? = some (.unenumerated node scs) → node = none ∧ scs = []
