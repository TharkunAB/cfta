/-- Replay the actual successful check without a lookup premise on unused branches. -/
theorem checkRepeated_replays
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended) :
    EnumerationFlatReplay.Replays (checkRepeated (EnumGuard := EnumGuard) heap uv handle scs)
      (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs) := by
  unfold checkRepeated SourcePruningEnumerationRecursion.checkRepeated
  cases decoded : lookupNode heap handle with
  | none =>
      intro flat earlier result after _ observed
      exact (EnumerationCorrectness.success_failure .unresolvedReference earlier after result observed).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [boundary, ↓reduceIte]
        apply EnumerationFlatReplay.bind_replays _ _ _ _
          (EnumerationFlatReplay.representative_replays fuel uv)
        intro root flat earlier result after related observed
        simp only [EnumerationCorrectness.Success, Bind.bind, StateT.bind, ExceptT.bind,
          ExceptT.bindCont, ExceptT.mk, get, getThe, MonadStateOf.get, StateT.get,
          Pure.pure, ExceptT.pure, ExceptT.run, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at observed ⊢
        change EnumerationCorrectness.Success
          (if recursionKey handle scs ∈ earlier.recursionAncestry root then
            EnumerationState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
           else pure false) earlier result after at observed
        change ∃ next,
          ((if recursionKey handle scs ∈ flat.recursionAncestry root then
              EnumerationFlatState.setValue root (.unenumerated (some handle) []) >>= fun _ => pure true
            else pure false) flat) = [.ok (result, next)] ∧ Related next after
        rw [related.recursionAncestry]
        by_cases seen : recursionKey handle scs ∈ earlier.recursionAncestry root
        · simp only [seen, ↓reduceIte] at observed ⊢
          obtain ⟨token, middle, written, returned⟩ :=
            (EnumerationCorrectness.success_bind _ _ earlier result after).mp observed
          cases token
          have shape := (EnumerationDriver.modify_success _ earlier middle).mp written
          obtain ⟨rfl, rfl⟩ := (EnumerationCorrectness.success_pure true result middle after).mp returned
          refine ⟨{flat with values := flat.values.set root (.unenumerated (some handle) [])}, rfl, ?_⟩
          rw [shape]
          exact ⟨related.valid, related.representatives, related.counter,
            congrArg (fun values => values.set root (.unenumerated (some handle) [])) related.values,
            related.obligations, related.recursionAncestry, related.expansionAncestry⟩
        · simp only [seen, ↓reduceIte] at observed ⊢
          obtain ⟨rfl, rfl⟩ := (EnumerationCorrectness.success_pure false result earlier after).mp observed
          exact ⟨flat, rfl, related⟩
      · simp only [boundary]
        exact EnumerationFlatReplay.pure_replays false
