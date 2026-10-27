theorem IsolatedPending.through_protected
    (isolated : IsolatedPending held handle before)
    (protectedRoot : EnumerationDriver.Protected held before after)
    (scs : List Suspended) (inputs : Avoids before.representatives held scs)
    (effects : ∀ allowed, ReferencesAllowed allowed before → InputsAllowed allowed scs →
      ReferencesAllowed allowed after) : IsolatedPending held handle after := by
