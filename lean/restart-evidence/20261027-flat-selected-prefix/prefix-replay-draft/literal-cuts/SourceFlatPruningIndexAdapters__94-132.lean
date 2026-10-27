/-- A completed old parked adapter supplies the related flat cache at the same observation. -/
theorem parked_completed (related : Related flat earlier)
    (checked : EnumerationFlatState.Related flatChecked earlierChecked)
    (heap : InternedConstructorTemplates.State Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (fuel uv handle : Nat) (scs : List Suspended)
    (completed : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs earlier earlierChecked = some after) :
    ∃ next, parked heap uv handle scs flat flatChecked = some next ∧ Related next after := by
  obtain ⟨written, observed, final⟩ := Option.map_eq_some_iff.mp completed
  obtain ⟨flatWritten, flatObserved, states⟩ := SourceFlatPruningCompletedIndex.write_related
    (frame_related related checked) heap fuel uv (.unenumerated (some handle) []) [] scs observed
  refine ⟨frame flatChecked flatWritten, ?_, ?_⟩
  · simp only [parked, flatObserved, Option.map_some]
  · subst after
    exact frame_related states checked

/-- A completed old narrowing adapter supplies the related actual flat endpoint. -/
theorem narrowed_completed (related : Related flat earlier)
    (observed : EnumerationFlatState.Related flatObserved earlierObserved)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (completed : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
      earlier earlierObserved = some after) :
    ∃ next, narrowed heap uv oldHandle newHandle scs flat flatObserved = some next ∧ Related next after := by
  by_cases same : newHandle = oldHandle
  · simp only [SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte, Option.some.injEq] at completed
    refine ⟨frame flatObserved flat, ?_, ?_⟩
    · simp only [narrowed, same, ↓reduceIte]
    · rw [← completed]
      exact frame_related related observed
  · simp only [SourcePruningEnumerationNarrowAdapter.adapt, same, ↓reduceIte] at completed
    obtain ⟨written, indexed, final⟩ := Option.map_eq_some_iff.mp completed
    obtain ⟨flatWritten, flatIndexed, states⟩ := SourceFlatPruningCompletedIndex.write_related
      (frame_related related observed) heap fuel uv (.unenumerated (some newHandle) scs) scs scs indexed
    refine ⟨frame flatObserved flatWritten, ?_, ?_⟩
    · simp only [narrowed, same, ↓reduceIte, flatIndexed, Option.map_some]
    · subst after
      exact frame_related states observed

end MicroCFTA.SourceFlatPruningIndexAdapters
