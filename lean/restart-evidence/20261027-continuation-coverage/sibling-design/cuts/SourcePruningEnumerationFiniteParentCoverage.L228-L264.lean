  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  have parentAccepted : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (.node parentEntry storedEdges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap packet.context.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free available selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  have recursive : SourcePruningEnumerationRecursive.Complete (bits := bits)
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel :=
    SourcePruningEnumerationRecursive.finite_complete
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result,
    running, post, captured, returnedFits, returnedKnown, length, receipts, outputResources, shape, accepting⟩ :=
    alternatives_finite_complete_resources_accepting
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges
      selectedEdges depth free packet ready stored decoded (fun edge member => selectedRows.mem_iff.mp member)
      incoming bounded known selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  refine ⟨bound, processed, outputs, afterCaller, next, final, result,
    ⟨running, post, captured, returnedFits, returnedKnown, length, receipts, outputResources, shape, accepting⟩,
    index, chosen, found, accepted, ?_⟩
  intro extra
  exact accepting extra index chosen found prefixSupported ambient assignment satisfied accepted
