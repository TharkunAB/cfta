theorem checkRepeated_canonical {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (canonical : Canonical before)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : Canonical after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before repeated after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after repeated impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have resolvedCanonical := representative_canonical fuel uv root before resolved canonical resolution
        obtain ⟨current, reading, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, readingSame⟩ := (EnumerationDriver.get_success resolved reading current).mp read
        subst current
        subst reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          have writtenCanonical := setValue_canonical root (.unenumerated (some handle) [])
            resolved written resolvedCanonical
            (by simp [EnumerationSchedule.references, ValidSuspended]) writing
          obtain ⟨_same, afterSame⟩ := (success_pure true repeated written after).mp finished
          simpa only [afterSame] using writtenCanonical
        · rw [ite_eq_right seen] at continued
          obtain ⟨_same, afterSame⟩ := (success_pure false repeated resolved after).mp continued
          simpa only [afterSame] using resolvedCanonical
      · have pureObserved : Success (pure false) before repeated after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        obtain ⟨_same, afterSame⟩ := (success_pure false repeated before after).mp pureObserved
        simpa only [afterSame] using canonical

/-- A successful prepared nonempty action keeps the original valid bucket. -/
theorem prepared_nonempty_canonical {Typing Key : Type}
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol Constraint → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : InternedConstructorTemplates.Value Symbol Constraint)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (checked after : EnumerationState.State Symbol Constraint)
    (canonical : Canonical checked) (valid : ValidSuspended scs)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) : Canonical after := by
  have actual := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
    nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
    narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at observed
    obtain ⟨_same, afterSame⟩ := (success_pure () () checked after).mp observed
    simpa only [afterSame] using canonical
  · rw [ite_eq_right same] at observed
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
    apply setValue_canonical selected (.unenumerated (some newHandle) scs) resolved after
      (representative_canonical representativeFuel uv selected checked resolved canonical reading)
    · exact valid
    · exact writing

end MicroCFTA.SourcePruningEnumerationSelectedPrefixCanonical
