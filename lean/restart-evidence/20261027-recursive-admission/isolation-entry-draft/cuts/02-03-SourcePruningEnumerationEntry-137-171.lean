        rw [compressedEq]
        exact representative_storage readAfter readStorage captureFuel uv inside captured captureRun
      obtain ⟨decoded, decodedLookup, available, closed⟩ := realized target handle scs (by
        simpa only [fullFrame.values] using storedCapture)
      let entered : EnumerationState.State Symbol EnumGuard :=
        {compressed with expansionAncestry :=
          if MergedOrdinaryHeight.recursiveBoundary decoded then
            (recursionKey handle scs :: compressed.recursionAncestry target).eraseDups
          else compressed.recursionAncestry target}
      have enteredStorage : StorageValid entered := by
        exact ⟨compressedStorage.aligned, compressedStorage.total, compressedStorage.forest,
          compressedStorage.values, compressedStorage.guards⟩
      have enteredRealized : PendingRealized heap entered := by
        intro slot node scs stored
        apply realized slot node scs
        simpa only [entered, fullFrame.values] using stored
      refine ⟨readFuel + captureFuel, .unenumerated (some handle) scs, readAfter, ?_, readFrame,
        target, decoded, compressed, entered, fullFrame, ?_, storedCapture,
        decodedLookup, available, closed, rfl, ?_, enteredStorage, enteredRealized⟩
      · intro extra
        simpa only [Nat.add_assoc] using readExact (captureFuel + extra)
      · intro extra
        exact captureExact extra
      · intro extra
        change enter heap (readFuel + captureFuel + extra) uv before = _
        unfold enter
        rw [bind_single _ _ before readAfter _ (by
          change ExceptT.run (getValue (readFuel + captureFuel + extra) uv before) = _
          simpa only [Nat.add_assoc] using readExact (captureFuel + extra))]
        dsimp only
        rw [bind_single _ _ readAfter compressed target (captureExact extra)]
        simp only [decodedLookup]
        rfl

end MicroCFTA.SourcePruningEnumerationEntry
