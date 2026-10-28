/-- Classify the actual decoded node without replacing a missing handle. -/
def candidate
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (value : EnumerationState.UVarValue Symbol) : Option Bool :=
  match value with
  | .unenumerated node scs =>
      match node with
      | none => some false
      | some handle =>
          (lookupNode heap handle).map fun decodedValue =>
            !(MergedOrdinaryHeight.recursiveBoundary decodedValue && scs.isEmpty)
  | .enumerated _ | .eliminated => some false
