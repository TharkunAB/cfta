      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationFiniteReservation.final_ge recursiveFuel seed ceiling
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_, resources.mono growth.1 growth.2⟩
    intro extra
    rw [(callback extra).2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (callbackFuel + extra) recursiveFuel)
      stop order, ite_eq_left rejected]
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
