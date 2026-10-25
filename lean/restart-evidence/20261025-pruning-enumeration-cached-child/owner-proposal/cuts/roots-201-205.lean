/-- Suspended references carried by one live pending slot. -/
def references : UVarValue Symbol → List Suspended
  | .unenumerated _ scs => scs
  | _ => []

