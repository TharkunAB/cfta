/-- Remaining pending slots are unrestricted equality variables. -/
def Discharged (state : State Symbol EnumGuard) : Prop :=
  ∀ (uv : Nat) (node : Option Nat) (scs : List EnumerationState.Suspended), state.values[uv]? = some (.unenumerated node scs) → node = none ∧ scs = []
