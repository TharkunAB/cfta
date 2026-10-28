    have model := satisfied.1.2 uv
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at model
    exact model.2
  obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry storedEdges depth free edge scs packet.context parentAvailable selected ambient assignment
      (assignment uv) accepted inheritedModel
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet bounded known
    parentEntry storedEdges depth free parentAvailable edge selected
  have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have actualCost : edgeCost scs before.core.counter edge =
      SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
    simp only [edgeCost, allowed, ↓reduceIte, projected]
  have actualReserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [actualCost] using reserved.edge costBound
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  have avoids := ready.avoids handle scs stored
  obtain ⟨r, n, p, h, k, actualCaller, middle, actualSaved, _final, _next, afterRoots, edgeResult,
    ⟨edgeRun, _post, _querySame, _growth, middlePaths, middleStorage, middleRealized, middleCounts,
    middleFlags, _origin, _retained, protects, _pendingHistory, _incomingHistory, shape,
    _returnedFits, _returnedKnown, _edgeAccepting⟩, edgeAccepting⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments_resources_origins seed formulas solver
      inventory caller before checkEmpty parentEntry storedEdges depth free edge scs roots memos packet.context
      parentAvailable parentClosed selected ready.safe realized paths counts flags bucketBound pending
      allowed tries residual projected bounded actualReserved known
  obtain ⟨terms, termShape, childrenAccepted, guardHolds⟩ :=
    (InternedGuardedLanguage.edgeMeaning_all
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv)).mp accepted
  obtain ⟨extended, fragment, agree, originalSatisfied, completed, filled, middleSatisfied, middleOrigins⟩ :=
    edgeAccepting ambient assignment terms whole satisfied childrenAccepted
      (by simpa only [termShape] using guardHolds)
      (by simpa only [termShape] using inheritedModel) origins
      (by simpa only [termShape] using origins uv ready.inside)
  rcases shape with ⟨built, builtComplete, _middleSafe, fragmentBound, _fragmentPending, _fragmentSeparate⟩ |
    ⟨_fragments, _outer, _waiting, stopped⟩
  · have sameFragment : built = fragment :=
      (SourcePruningEnumerationSelectedEdge.Result.complete.inj (builtComplete.symm.trans completed)).1
    subst built
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨fuel, after, finishRun, _raw, written, _finalStored, _finalFlag, _finalWaiting,
      _afterPaths, _afterCounts, _afterFlags, _afterStorage, _afterRealized, _afterSafe⟩ :=
      SourcePruningEnumerationFinalize.complete actualCaller.checked.native.machine.heap middle uv fragment
        (.unenumerated (some handle) scs) currentStored afterRoots middlePaths middleCounts middleFlags
        middleStorage fragmentBound middleRealized
    let padding := r + n + p + h + k + fuel
    let work := bound + padding
    have rl : r ≤ work := by dsimp [work, padding]; omega
    have nl : n ≤ work := by dsimp [work, padding]; omega
    have pl : p ≤ work := by dsimp [work, padding]; omega
    have hl : h ≤ work := by dsimp [work, padding]; omega
    have kl : k ≤ work := by dsimp [work, padding]; omega
    have fl : fuel ≤ work := by dsimp [work, padding]; omega
    have selectedAt := edgeRun (work - r) (work - n) work work (work - k) pl hl
    simp only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl, builtComplete] at selectedAt
    have finalizedAt := finishRun (work - fuel)
    simp only [Nat.add_sub_of_le fl] at finalizedAt
    have capturedAt : SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work
        uv scs edge caller before memos.query = some (.complete fragment actualCaller actualSaved after) := by
      simp only [SourcePruningEnumerationCapturedEdge.run, selectedAt, finalizedAt, Option.map_some]
    have receiptSame : receipt = .complete fragment actualCaller actualSaved after :=
      Option.some.inj ((running padding).symm.trans capturedAt)
    have reached : advance receipt = some (middleCaller, saved) := by
      rcases headShape with ⟨unsupported, _allowed, _projected⟩ |
        ⟨_outcome, advanced, _callback, _resources, _captured⟩
      · rw [receiptSame] at unsupported
        cases unsupported
      · simpa only [headQueries] using advanced
    rw [receiptSame] at reached
    change some (actualCaller, actualSaved) = some (middleCaller, saved) at reached
    have sameEndpoint := Option.some.inj reached
    have sameCaller : actualCaller = middleCaller := congrArg Prod.fst sameEndpoint
    have sameQueries : actualSaved = saved := congrArg Prod.snd sameEndpoint
    have finalSatisfied : Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient actualCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        extended after.core := by
      have selfValue : Fragments.fill extended fragment = extended uv :=
        (filled.trans termShape.symm).trans (agree uv ready.inside).symm
      exact (SourcePruningEnumerationFinalize.written_semantics middle.core after.core uv fragment
        (List.getElem?_eq_some_iff.mp currentStored).1 written
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient actualCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) extended).mpr
        ⟨EnumerationFrame.neutralize_satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient actualCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended uv middle.core middleSatisfied, selfValue⟩
    refine ⟨extended, fragment, after, agree, originalSatisfied, ?_, filled.trans termShape.symm, ?_⟩
    · simpa only [sameCaller, sameQueries] using receiptSame
    · refine ⟨?_, ?_⟩
      · simpa only [sameCaller] using finalSatisfied
      · simpa only [written] using middleOrigins
  · rw [stopped] at completed
    cases completed

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
