  | nil =>
      refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
        .complete [] beforeCaller memos.query before, ?_, Post.refl initial, rfl, Nat.le_refl _,
        paths, safe.1, realized, counts, flags, .refl _, ?_, ?_, (fun _ valid _ => valid),
        (fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩, fits, known, ?_⟩
      · intros; rfl
      · intro held fragment stored
        exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core safe held fragment stored).2
      · intro held _ root _
        exact EnumerationDriver.Protected.refl held before.core root
      · simp
      · intro carried
        exact ⟨.refl before.core, carried, by simp⟩
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      obtain ⟨r, n, p, h, k, raw, middleCaller, middle, middleQueries, middleMemos, middleInventory,
        middleRoots, outer, waiting, headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape, middleFits, middleKnown⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed formulas solver inventory beforeCaller before
          checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending available closed fits
          (reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)) known
      have protects : ∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
          EnumerationDriver.Protected held before.core middle.core := by
        intro held fragment stored
        obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment stored
        exact headProtected held inside root (pending held fragment stored)
      rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩
      · subst raw
        refine ⟨r, n, p, h, k, [], middleCaller, middle, middleQueries, middleMemos, middleInventory,
          middleRoots, .stopped [] (.ok (some []), middleCaller, middleQueries, outer, waiting) (some middle),
          ?_, headPost, headQueries, growth, middlePaths, middleStorage, middleRealized, middleCounts,
          middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationChildTraversal.run, headRun er en P H ek largeP largeH]
        · intro held inside root avoids
          exact headProtected held inside root (avoids incoming bucket (by simp))
        · intro allowed valid allowedInputs
          exact headReferences allowed valid (allowedInputs incoming bucket (by simp))
        · simp
        · change Fits (advance seed ((bucket.length + 1) + cost rest)).2 middleCaller.checked
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          exact middleFits.mono
            (SourcePruningEnumerationIncomingReservation.advance_profile_ge (advance seed (bucket.length + 1)) (cost rest))
        · change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            middleCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationIncomingReservation.advance_add]
          intro key edge found
          exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
            (advance seed (bucket.length + 1)) (cost rest) (middleKnown key edge found)
        · intro carried
          have actual := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
          simp only [Nat.add_zero] at actual
          have carrierFacts := SourcePruningEnumerationChildDispatch.candidate_carriers
            checkEmpty r n p h k bucket incoming beforeCaller before memos.query safe carried middle
            (by rw [actual])
          exact ⟨carrierFacts.2.1, carrierFacts.2.2, by simp⟩
      · have tailGenuine : ∀ value bucket, (value, bucket) ∈ rest →
            Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
            (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value retained member
          obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
            genuine value retained (List.mem_cons_of_mem _ member)
          refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
            fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
          intro held storedFragment stored
