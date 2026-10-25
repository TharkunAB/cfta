def references : UVarValue Symbol → List Suspended
  | .unenumerated _ scs => scs
  | _ => []

