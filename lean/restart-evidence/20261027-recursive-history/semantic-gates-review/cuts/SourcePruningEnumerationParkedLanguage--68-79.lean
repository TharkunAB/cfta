theorem checkRepeated_true_satisfies
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel uv handle : Nat) (scs : List Suspended)
    (before after : State Symbol EnumGuard)
    (ready : EnumerationDriver.Ready uv before)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (observed : Success (checkRepeated heap fuel uv handle scs) before true after) :
    Satisfies language meaning assignment before ↔
      Satisfies language meaning assignment after ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
  cases decoded : lookupNode heap handle with
