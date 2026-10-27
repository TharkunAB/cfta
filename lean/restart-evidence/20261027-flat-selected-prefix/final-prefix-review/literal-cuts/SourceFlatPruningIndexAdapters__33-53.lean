/-- The parked cache retains the actual observed core. -/
theorem parked_core (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv handle : Nat) (scs : List Suspended) (before after : Cached Symbol EnumGuard)
    (checked : EnumerationFlatState.State Symbol EnumGuard)
    (completed : parked heap uv handle scs before checked = some after) : after.core = checked := by
  obtain ⟨written, _indexed, final⟩ := Option.map_eq_some_iff.mp completed
  subst after
  rfl

/-- The narrowing cache retains the actual observed core on both handle branches. -/
theorem narrowed_core (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (uv oldHandle newHandle : Nat) (scs : List Suspended) (before after : Cached Symbol EnumGuard)
    (observed : EnumerationFlatState.State Symbol EnumGuard)
    (completed : narrowed heap uv oldHandle newHandle scs before observed = some after) : after.core = observed := by
  unfold narrowed at completed
  split at completed
  · cases completed
    rfl
  · obtain ⟨written, _indexed, final⟩ := Option.map_eq_some_iff.mp completed
    subst after
    rfl
