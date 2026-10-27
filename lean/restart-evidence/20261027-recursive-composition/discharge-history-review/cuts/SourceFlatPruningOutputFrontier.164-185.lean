/-- Discharge additionally removes native pending handles and pure pending constraints. -/
theorem discharged_iff (before : Cached)
    (earlier : EnumerationExpandableIndex.Cached Symbol Constraint)
    (related : EnumerationFlatCached.Related before earlier) :
    SourcePruningEnumerationRendering.Discharged earlier.core ↔
      (∀ (uv handle : Nat) (scs : List Suspended), before.core.values[uv]? ≠ some (.unenumerated (some handle) scs)) ∧
      (∀ (uv : Nat) (scs : List Suspended), before.core.values[uv]? = some (.unenumerated none scs) → scs = []) := by
  constructor
  · intro discharged
    constructor
    · intro uv handle scs stored
      have impossible := discharged uv (some handle) scs
        (by simpa only [related.core.values] using stored)
      cases impossible.1
    · intro uv scs stored
      exact (discharged uv none scs (by simpa only [related.core.values] using stored)).2
  · rintro ⟨noHandle, noConstraints⟩ uv node scs stored
    have flatStored : before.core.values[uv]? = some (.unenumerated node scs) := by
      simpa only [related.core.values] using stored
    cases node with
    | none => exact ⟨rfl, noConstraints uv scs flatStored⟩
    | some handle => exact False.elim (noHandle uv handle scs flatStored)
