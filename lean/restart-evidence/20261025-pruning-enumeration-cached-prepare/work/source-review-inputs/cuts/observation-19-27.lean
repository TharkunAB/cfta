def PendingRealized (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : EnumerationState.State Symbol EnumGuard) : Prop :=
  ∀ (slot node : Nat) (scs : List EnumerationState.Suspended),
    state.values[slot]? = some (.unenumerated (some node) scs) →
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        lookupNode heap node = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = []

/-- A closed available input derives the handle in the actual initial slot. -/
