  obtain ⟨readFuel, oldHandle, scs, oldValue, readAfter, checkFuel, repeated, checked, stored, oldDecoded,
    _oldAvailable, _oldClosed, readExact, checkExact, checkReady, checkPaths, checkRealized,
    checkCounts, checkFlags, _checkIncoming, checkPending, parked, continued⟩ :=
    SourcePruningEnumerationSelectedOrdinary.complete_with_history formulas solver inventory caller memos
      holeKey fits admits metadata graph templates checkEmpty edgesOf before preference uv roots
      initial safe pending selection realized paths counts flags
  cases repeated with
  | true =>
      obtain ⟨_boundary, _cleared, _disabled, _waiting, resolved, countFuel, frame, _reading,
        _seen, written, indexed⟩ := parked rfl
      obtain ⟨counter, ordered⟩ := SourcePruningEnumerationParkedRestart.parked_order uv oldHandle scs
        before.core resolved checked.core stored frame written
      let bound := readFuel + checkFuel + countFuel
      refine ⟨bound, ?_⟩
      intro extra
      let w := bound + extra
      have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
      have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
      have countLe : countFuel ≤ w := by dsimp [w, bound]; omega
      have reading := readExact (w - readFuel)
      have checking := checkExact (w - checkFuel)
      rw [Nat.add_sub_of_le readLe] at reading
      rw [Nat.add_sub_of_le checkLe] at checking
      have index := indexed (w - countFuel)
      rw [Nat.add_sub_of_le countLe] at index
      have adapted := SourcePruningEnumerationParkedRestart.adapt_after_write caller.checked.native.machine.heap
        w uv oldHandle scs before checked resolved checked.core written index rfl
      have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
          uv caller before memos.query = .parked checked.core (some checked)
          (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata checked checked.core))) := by
        simp only [runPrefix, reading, checking, adapted, Option.map_some]
      refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
        w w w w w w uv caller before memos.query, ?_, ?_⟩
      · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
          (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv caller before memos.query)
        rw [run_parked holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
          w w w w w w 0 0 0 0 0 uv oldHandle scs caller before checked memos.query
          readAfter checked.core reading checking adapted]
        exact ⟨oldHandle, scs, readAfter, reading, checking, checked, rfl, rfl,
          ⟨roots, checkPaths, checkReady.safe.1, checkRealized, checkCounts, checkFlags⟩,
          checkReady.safe, checkPending pending, counter, ordered, rfl⟩
      · rw [prefixRun]
        exact ⟨counter, ordered⟩
  | false =>
      obtain ⟨value, nativeFuel, heap, newHandle, final, narrowed, stable, post, _retained, query,
        _available, _closed, encoded, _decoded, rejected, completed⟩ := continued rfl
      by_cases empty : value = .empty
      · subst value
        let bound := readFuel + checkFuel + nativeFuel
        refine ⟨bound, ?_⟩
        intro extra
        let w := bound + extra
        have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
        have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
        have nativeLe : nativeFuel ≤ w := by dsimp [w, bound]; omega
        have reading := readExact (w - readFuel)
        have checking := checkExact (w - checkFuel)
        rw [Nat.add_sub_of_le readLe] at reading
        rw [Nat.add_sub_of_le checkLe] at checking
        obtain ⟨prepared, _noSuccess⟩ := rejected rfl w
        have preparedAt := SourcePruningEnumerationPreparedFuel.native_moreFuel holeKey fits admits metadata
          nativeFuel w uv oldHandle (w - nativeFuel) scs oldValue .empty caller.checked.native.machine.heap
          heap (some reject) narrowed stable prepared
        rw [Nat.add_sub_of_le nativeLe] at preparedAt
        have narrowedAt := stable (w - nativeFuel)
        rw [Nat.add_sub_of_le nativeLe] at narrowedAt
        have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
            uv caller before memos.query =
            .narrowed checked.core (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
              memos.query (some []) none none none := by
          simp only [runPrefix, reading, checking, oldDecoded, preparedAt]
          rfl
        refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
          w w w w w w uv caller before memos.query, ?_, ?_⟩
        · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
            (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
              w w w w w w 0 0 0 0 0 uv caller before memos.query)
          rw [run_empty holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv oldHandle scs oldValue caller before memos.query
            readAfter checked.core heap reading checking oldDecoded preparedAt]
          exact ⟨oldHandle, scs, readAfter, reading, checking, oldValue, .empty, heap, reject,
            final, oldDecoded, narrowedAt, preparedAt, rfl, rfl, rfl, post, query,
            Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        · rw [prefixRun]
          trivial
