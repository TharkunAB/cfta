/-- Retain the optional node and reject its empty handle before writes. -/
def finishOptional (source target : Nat) (node : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) :
    EnumerateM Symbol EnumGuard Unit :=
  fun state =>
    if node = some 0 then [] else
      [.ok ((), assimilated state target source (.unenumerated node (sourceScs ++ targetScs)))]
