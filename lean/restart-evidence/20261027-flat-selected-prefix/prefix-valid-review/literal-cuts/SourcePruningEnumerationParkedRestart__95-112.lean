def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel uv handle : Nat) (scs : List Suspended)
    (before : Cached) (checked : EnumerationState.State Symbol Constraint) : Option Cached :=
  (SourcePruningEnumerationNativeIndex.write heap indexFuel uv (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before)).map (EnumerationExpandableIndex.frame checked)

/-- An attached parked cache retains the exact observed check endpoint. -/
theorem adapt_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel uv handle : Nat) (scs : List Suspended)
    (before after : Cached) (checked : EnumerationState.State Symbol Constraint)
    (adapted : adapt heap indexFuel uv handle scs before checked = some after) :
    after.core = checked := by
  simp only [adapt, Option.map_eq_some_iff] at adapted
  obtain ⟨cached, _written, same⟩ := adapted
  subst after
  rfl
