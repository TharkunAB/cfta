    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol Constraint → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : InternedConstructorTemplates.Value Symbol Constraint)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (checked after : EnumerationState.State Symbol Constraint)
    (total : UnionFind.Total checked.representatives) (references : ReferencesCarry checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers checked after ∧ ReferencesCarry after := by
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
    subst after
    exact ⟨total, .refl _, references⟩
  · rw [ite_eq_right same] at observed
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
    have frame := representative_frame representativeFuel uv selected checked resolved total reading
    have written := pending_write_carriers selected newHandle scs resolved after
      (frame.total total) (frame.references references) writing
    exact ⟨written.1, frame.carriers.trans written.2.1, written.2.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedPrefixCarriers
