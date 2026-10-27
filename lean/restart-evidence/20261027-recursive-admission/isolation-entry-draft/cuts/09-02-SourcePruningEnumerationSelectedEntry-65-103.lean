    exact fullFrame.values
  have classes : ∀ left right, UnionFind.SameClass after.core.representatives left right ↔
      UnionFind.SameClass before.core.representatives left right := by
    intro left right
    simp only [after, EnumerationExpandableIndex.frame, ancestry, UnionFind.SameClass, fullFrame.reaches]
  have safe : Safe after.core := by
    rw [show after.core = entered from rfl, ancestry]
    exact EnumerationDriver.ancestry_safe compressed _ compressedSafe
  have frame : EnumerationDriver.Protected uv before.core after.core := by
    have compressedFrame := readProtection.trans captureProtection
    refine ⟨?_, ?_, classes uv⟩
    · rw [values]
    · rw [show after.core = entered from rfl, ancestry]
      exact compressedFrame.root
  have afterReady : EnumerationDriver.Ready uv after.core := by
    refine ⟨safe, by simpa only [counter] using ready.inside, frame.root, ?_⟩
    intro node bucket read
    exact frame.avoids bucket (ready.avoids node bucket (by simpa only [values] using read))
  have afterPaths : Roots after.core.representatives roots := by
    intro slot
    obtain ⟨size, path⟩ := paths slot
    refine ⟨size, ?_⟩
    rw [show after.core = entered from rfl, ancestry]
    exact (fullFrame.reaches slot (roots slot) size).mpr path
  have actualStored : after.core.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [values] using stored
  refine ⟨fuel, decoded, after, entryRun, decodedLookup, available, closed, counter, values,
    rfl, rfl, actualStored, afterReady, frame, afterPaths, enteredRealized, ?_, ?_,
    safe.1.values _ (List.mem_of_getElem? actualStored), ?_, ?_⟩
  · simpa only [values, show after.waiting = before.waiting from rfl] using counts
  · simpa only [values, show after.expandable = before.expandable from rfl] using flags
  · intro bucket pending held fragment expanded sc member sameClass
    exact pending held fragment (by simpa only [values] using expanded) sc member
      ((classes held sc.var).mp sameClass)
  · refine ⟨safe, counter, values, ?_, classes⟩
    rw [show after.core = entered from rfl, ancestry]
    exact fullFrame.obligations

end MicroCFTA.SourcePruningEnumerationSelectedEntry
