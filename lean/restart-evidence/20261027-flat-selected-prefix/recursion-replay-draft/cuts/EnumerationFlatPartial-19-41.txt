/-- Read the current direct root and its stored value without old lookup fuel. -/
theorem getValue_replays (fuel uv : Nat) :
    Replays (Symbol := Symbol) (Guard := Guard)
      (getValue uv) (EnumerationState.getValue fuel uv) := by
  apply bind_replays _ _ _ _ (representative_replays fuel uv)
  intro root flat earlier value after related observed
  simp only [EnumerationCorrectness.Success, EnumerationState.rawValue, Bind.bind,
    get, getThe, MonadStateOf.get, StateT.bind, StateT.get, ExceptT.bind,
    ExceptT.pure, ExceptT.bindCont, ExceptT.mk, Pure.pure,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, ExceptT.run] at observed
  cases stored : earlier.values[root]? with
  | none =>
      simp only [stored] at observed
      change Except.ok (value, after) ∈ [Except.error EnumerationState.Error.invalidSlot] at observed
      simp only [List.mem_singleton] at observed
      cases observed
  | some found =>
      have same : value = found ∧ after = earlier := by
        simp only [stored] at observed
        change Except.ok (value, after) ∈ [Except.ok (found, earlier)] at observed
        simpa only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] using observed
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨flat, by simp [rawValue, related.values, stored], related⟩
