    | union entry members depth free =>
        refine ⟨(allocate (some node) >>= fun uv => pure (.hole uv)),
          allocated (some node) before, ?_, ?_, rfl, allocatedSlot, rfl,
          allocated_supply (some node) before aligned, allocatedRealized⟩
        · simp [prepareChild, nonterminal, encoded]
        · exact (success_bind _ _ _ _ _).mpr
            ⟨before.counter, allocated (some node) before, allocation,
              (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
    | mu entry body depthShape ordinaryShape =>
        refine ⟨(allocate (some node) >>= fun uv => pure (.hole uv)),
          allocated (some node) before, ?_, ?_, rfl, allocatedSlot, rfl,
          allocated_supply (some node) before aligned, allocatedRealized⟩
        · simp [prepareChild, nonterminal, encoded]
        · exact (success_bind _ _ _ _ _).mpr
            ⟨before.counter, allocated (some node) before, allocation,
              (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩

end MicroCFTA.SourcePruningEnumerationShallowChild
