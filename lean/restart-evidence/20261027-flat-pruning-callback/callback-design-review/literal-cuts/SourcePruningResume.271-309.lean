theorem resume_complete (current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before : State Symbol Guard)
    (total : UnionFind.Total before.representatives) :
    ∃ (fuel : Nat) (result : Option (Pending Symbol)) (after : State Symbol Guard),
      Success (resume fuel current term pending) before result after ∧ Frame before after := by
  have step : ∀ (pendingPart : Template.Pattern Symbol × Nat) (previous : State Symbol Guard),
      UnionFind.Total previous.representatives →
        ∃ (fuel : Nat) (result : Option (Pending Symbol)) (next : State Symbol Guard),
          Success (part fuel current term pendingPart) previous result next ∧
            UnionFind.Total next.representatives := by
    intro pendingPart previous previousTotal
    obtain ⟨fuel, root, next, reading, nextTotal⟩ :=
      representative_terminates previous previousTotal pendingPart.2
    refine ⟨fuel, (if root = current then matchPartial pendingPart.1 term else some [(pendingPart.1, root)]),
      next, ?_, nextTotal⟩
    exact (part_success fuel current term pendingPart previous next _).mpr ⟨root, reading, rfl⟩
  obtain ⟨fuel, results, after, traversed, _afterTotal⟩ :=
    mapM_terminates (fun fuel pendingPart => part fuel current term pendingPart)
      (fun state : State Symbol Guard => UnionFind.Total state.representatives)
      (fun fuel extra pendingPart => part_moreFuel fuel extra current term pendingPart)
      step pending before total
  let result := (results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id)
  have completed : Success (resume fuel current term pending) before result after := by
    unfold resume
    exact (success_bind _ _ _ _ _).mpr
      ⟨results, after, traversed, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  exact ⟨fuel, result, after, completed, resume_frame fuel current term pending before after result total completed⟩

/-- Resuming allocated parked references preserves safety and the rendering state. -/
theorem resume_read (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (safe : Safe before) (bounded : ∀ pendingPart ∈ pending, pendingPart.2 < before.counter)
    (success : Success (resume fuel current term pending) before result after) :
    EnumerationDriver.RenderStable before after := by
  unfold resume at success
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
  have step : ∀ pendingPart ∈ pending, ∀ previous output next,
      EnumerationDriver.RenderStable before previous →
        Success (part fuel current term pendingPart) previous output next →
