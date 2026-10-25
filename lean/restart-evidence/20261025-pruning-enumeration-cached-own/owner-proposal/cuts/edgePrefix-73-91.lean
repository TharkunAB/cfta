 := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte]
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => simp only [prepare, allowed, ↓reduceIte, projected]
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        dsimp only
        refine ⟨(tries.mapM suspend >>= fun own =>
          pure (edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)), residual)),
          ?_, ?_, EnumerationSchedule.suspended_counter tries.length before,
          suspended_supply tries.length before aligned, suspended_realized tries.length heap before realized⟩
        · simp only [prepare, allowed, ↓reduceIte, projected]
        · rw [bind_single _ _ before _ _ (suspendMany_exact tries before)]
          rfl
