    intro ambient assignment satisfied
    obtain ⟨neutralMiddle, equation⟩ :=
      (SourcePruningEnumerationFinalize.written_semantics middle.core after.core uv fragment
        (List.getElem?_eq_some_iff.mp currentStored).1 written
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment).mp satisfied
    obtain ⟨neutralBefore, edgeAccepted, parentAccepted, suspended⟩ := sound ambient assignment neutralMiddle
    have oldSlot : Fragments.slotSatisfies assignment uv
        (heap (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) before.core.values uv) := by
      simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies, List.forall_mem_map]
      constructor
      · rw [← equation]
        exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mpr parentAccepted
      · intro sc member
        rw [← equation]
        exact suspended sc member
    have original := EnumerationFrame.neutralize_restore
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment uv before.core neutralBefore oldSlot
    exact ⟨original, by simpa only [equation] using edgeAccepted,
      by simpa only [equation] using parentAccepted,
      by simpa only [equation] using suspended, equation⟩
  · subst result
    have selectedRun := edgeRun r n (max p p0) (max h h0) k
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
