          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenAvailable indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
        (by
          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenClosed indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
        (by
          intro input member
          obtain ⟨indexed, indexedMember, inputSame⟩ := List.mem_map.mp member
          subst input
          exact childrenNonempty indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember))
    rw [stagedSame] at childrenSuccess completedPrefixSuccess resultShape afterCounter
    rw [prefixCounter] at completedPrefixSuccess resultShape afterCounter
    refine ⟨prefixAction >>= fun packet =>
      runStaged packet.2.1 >>= fun childrenResult =>
        match childrenResult with
        | none => pure none
        | some fragments => EnumerationSchedule.recordResidual packet.2.2 (.node packet.1 fragments)
            >>= fun _ => pure (some (.node packet.1 fragments)),
      childrenResult, childrenAfter, _, ?_, childrenSuccess, completedPrefixSuccess,
      resultShape, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [prepare, prefixPrepared]
    · apply (success_bind _ _ _ _ _).mpr
      refine ⟨_, suspendedState tries.length before, prefixSuccess, ?_⟩
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨childrenResult, childrenAfter, childrenSuccess, ?_⟩
      cases childrenResult with
      | none => exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
      | some fragments =>
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨(), _, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        cases residual with
        | none => exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
        | some guard => exact (EnumerationDriver.modify_success _ _ _).mpr rfl
