theorem checkRepeated_canonical {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (canonical : Canonical before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : Canonical after := by
