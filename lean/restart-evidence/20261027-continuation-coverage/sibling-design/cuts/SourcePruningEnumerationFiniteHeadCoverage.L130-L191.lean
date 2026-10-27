    before.core.counter edge children own inheritedLength
  have pending := EnumerationReferences.pending_inputs before.core packet.pending uv (some handle) scs stored
  obtain ⟨r, n, p, h, k, receipt, middleCaller, saved, middleMemos, middleInventory,
    headRun, headPost, headQueries, admitted, headPending, history, shape, headFits, headKnown, accepting⟩ :=
    SourcePruningEnumerationNativeBranchCompletion.head_complete_resources_accepting seed formulas solver inventory caller before
      checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos packet.context ready stored decoded
      realized selected paths counts flags pending bounded (reserved.edge costBound) known
  have headRun0 := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at headRun0
  have cacheBounds := SourcePruningEnumerationNativeBranchCompletion.observed_head_cache_bounds
    checkEmpty r n p h k uv scs edge caller before memos.query
    (scalar seed.2) (guardWidth seed.1) children own receipt headRun0
  have padding := SourcePruningEnumerationRecursiveReservation.head_padding seed inherited
    (edgeCost scs before.core.counter edge) costBound
  have boundedHead := headFits.mono padding.1
  have knownHead : Heap (fun guard => guard ∈ (afterHead seed inherited).1)
      middleCaller.checked.native.machine.heap :=
    fun key resident found => padding.2 (headKnown key resident found)
  have receiptPending := headPending packet.pending incoming
  let headBound := r + n + p + h + k
  have headAt (w : Nat) (large : headBound ≤ w) :
      SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w uv scs edge caller before memos.query = some receipt := by
    have rl : r ≤ w := by dsimp [headBound] at large; omega
    have nl : n ≤ w := by dsimp [headBound] at large; omega
    have pl : p ≤ w := by dsimp [headBound] at large; omega
    have hl : h ≤ w := by dsimp [headBound] at large; omega
    have kl : k ≤ w := by dsimp [headBound] at large; omega
    have observed := headRun (w - r) (w - n) w w (w - k) pl hl
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using observed
  rcases shape with advanced | unsupported
  · have advancedQuery : advance receipt = some (middleCaller, middleMemos.query) := by
      simpa only [headQueries] using advanced
    have mass := SourcePruningEnumerationRecursiveReservation.head_mass_le seed capturedMass inherited
      before scs receipt initialMass inheritedLength cacheBounds
    obtain ⟨callbackFuel, outcome, callbackRun, resources⟩ := receipt_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver recursiveFuel recursive
      inventory middleInventory
      caller middleCaller memos middleMemos before uv receipt packet headPost advancedQuery admitted receiptPending history
      (afterHead seed inherited) (massCeil seed capturedMass inherited) boundedHead knownHead
      selectionMembers selectionLength (by cases receipt <;> exact mass) reserved.2
    have fullResources : OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome :=
      resources.post headPost
    refine ⟨headBound + callbackFuel, receipt, middleCaller, saved, middleMemos, middleInventory,
      ?_, headPost, headQueries, admitted, receiptPending, history, cacheBounds, boundedHead, knownHead,
      .inr ⟨outcome, advancedQuery, ?_, fullResources, ?_⟩, accepting⟩
    · intro extra
      exact headAt (headBound + callbackFuel + extra) (by omega)
    · intro extra
      have actual := callbackRun (headBound + extra)
      have common : callbackFuel + (headBound + extra) = headBound + callbackFuel + extra := by omega
      rw [common] at actual
      exact actual
    · cases outcome with
      | stopped _ _ _ => trivial
      | complete outputs actual queries =>
          obtain ⟨next, final, post, query, captured, returnedFits, returnedKnown, _outputs⟩ :=
            SourcePruningEnumerationRecursive.completed_captured_packet formulas solver inventory caller memos
              metadata before (finiteStep recursiveFuel seed capturedMass inherited) outputs actual queries packet fullResources
          exact ⟨next, final, post, query, captured, returnedFits, returnedKnown⟩
  · exact ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
      fun extra => headAt (headBound + extra) (by omega), headPost, headQueries,
      admitted, receiptPending, history, cacheBounds, boundedHead, knownHead, .inl unsupported, accepting⟩
