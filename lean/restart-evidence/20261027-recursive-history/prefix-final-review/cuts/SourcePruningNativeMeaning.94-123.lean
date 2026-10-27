/-- Mu and type skips or actual filtering return only terms of the original value. -/
theorem narrow_sound [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (guarded : InternedGuardedProbeHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrow holeKey fits admits metadata fuel uv value before = .done result after)
    (term : Term Symbol) (accepted : meaning holds ambient result term) :
    meaning holds ambient value term := by
  have skipped (same : result = value ∧ after = before) : meaning holds ambient value term := by
    obtain ⟨rfl, rfl⟩ := same
    exact accepted
  by_cases typed : uv ∈ metadata.types
  · have pureDone := narrow_type holeKey fits admits metadata fuel uv value before typed
    have parts := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨parts.1.symm, parts.2.symm⟩
  · cases value with
    | mu =>
        have parts := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨parts.1.symm, parts.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [narrow, typed] at narrowed
        exact SourcePruningNativeView.narrowAt_sound holds ambient fits admits
          (holeKey metadata.typing uv) fuel _ before result after ready guarded
          available closed narrowed term accepted
