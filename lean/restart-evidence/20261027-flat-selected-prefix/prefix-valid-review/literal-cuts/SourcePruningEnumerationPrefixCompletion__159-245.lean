      · obtain ⟨representativeFuel, countFuel, action, after, prepared, observed, shape, waiting, afterReady,
          afterPaths, afterRealized, afterStored, afterCounts, afterFlags, afterPending, _afterIncoming,
          _callback, ordinary⟩ := completed empty
        obtain ⟨indexFuel, adapted⟩ := SourcePruningEnumerationNarrowAdapter.complete heap uv oldHandle newHandle
          representativeFuel countFuel scs before after checked.core shape
        have readSuccess : Success (getValue readFuel uv) before.core
            (.unenumerated (some oldHandle) scs) readAfter := by
          rw [Success, ← Nat.add_zero readFuel, readExact 0]
          exact List.mem_singleton_self _
        have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
            caller.checked.native.machine.heap checkFuel uv oldHandle scs) readAfter false checked.core := by
          rw [Success, ← Nat.add_zero checkFuel, checkExact 0]
          exact List.mem_singleton_self _
        have history := SourcePruningEnumerationPrefixHistory.complete caller.checked.native.machine.heap
          before after readAfter checked.core readFuel checkFuel representativeFuel uv oldHandle newHandle scs
          safe stored readSuccess checkSuccess (by
            rcases shape with ⟨_same, equal⟩ | ⟨_different, resolved, reading, written, _indexed⟩
            · exact Or.inl equal
            · exact Or.inr ⟨resolved, reading, written⟩)
        let bound := readFuel + checkFuel + nativeFuel + representativeFuel + indexFuel
        refine ⟨bound, ?_⟩
        intro extra
        let w := bound + extra
        have readLe : readFuel ≤ w := by dsimp [w, bound]; omega
        have checkLe : checkFuel ≤ w := by dsimp [w, bound]; omega
        have nativeLe : nativeFuel ≤ w := by dsimp [w, bound]; omega
        have representativeLe : representativeFuel ≤ w := by dsimp [w, bound]; omega
        have indexLe : indexFuel ≤ w := by dsimp [w, bound]; omega
        have reading := readExact (w - readFuel)
        have checking := checkExact (w - checkFuel)
        rw [Nat.add_sub_of_le readLe] at reading
        rw [Nat.add_sub_of_le checkLe] at checking
        have adaptedAt := adapted (w - indexFuel)
        rw [Nat.add_sub_of_le indexLe] at adaptedAt
        obtain ⟨nextAction, preparedAt, raw⟩ := SourcePruningEnumerationPreparedFuel.nonempty_moreFuel
          holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value
          caller.checked.native.machine.heap heap action checked.core after.core narrowed stable empty encoded prepared
          observed (w - nativeFuel) (w - representativeFuel)
        rw [Nat.add_sub_of_le nativeLe, Nat.add_sub_of_le representativeLe] at preparedAt
        have narrowedAt := stable (w - nativeFuel)
        rw [Nat.add_sub_of_le nativeLe] at narrowedAt
        have right : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates w metadata uv
            (.inr newHandle) after.core) = [.ok ((false, metadata), after.core)] := by
          rw [SourcePruningRecordTypes.recordTypes_inr]
          rfl
        have prefixRun : runPrefix holeKey fits admits graph templates stop order metadata w w w w w w
            uv caller before memos.query = .narrowed checked.core (.done (value, some nextAction) heap)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
              memos.query (some [.ok ((), after.core)]) (some after)
              (some [.ok ((false, metadata), after.core)]) none := by
          simp only [runPrefix, reading, checking, oldDecoded, preparedAt, raw, encoded, adaptedAt, right]
          rfl
        refine ⟨prefix_no_ordinary holeKey fits admits graph templates stop order metadata
          w w w w w w uv caller before memos.query, ?_, ?_⟩
        · change Valid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            formulas solver inventory w w w w w w 0 0 0 0 0 uv caller before memos
            (run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
              w w w w w w 0 0 0 0 0 uv caller before memos.query)
          rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w 0 0 0 0 0 uv oldHandle newHandle scs oldValue value caller before after memos.query
            readAfter checked.core heap nextAction reading checking oldDecoded preparedAt raw encoded adaptedAt]
          refine ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, nextAction,
            final, oldDecoded, narrowedAt, preparedAt, rfl, rfl, rfl, post, query, Or.inr
              ⟨newHandle, after, empty, encoded, rfl, rfl,
                ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩,
                afterReady.safe, afterPending pending, afterReady, afterStored, waiting, rfl, rfl, ?_⟩⟩
          intro parentEntry storedEdges depth free parent nonterminal selected ranges
          obtain ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
            ordinaryRun, _render, _sameFlags, _sameWaiting, lastPost, lastQuery, admitted,
            receiptHistory, receiptPosts, fragments, callbacks, outcomeShape, supported⟩ :=
            ordinary parentEntry storedEdges depth free parent nonterminal selected (by simpa only [query] using ranges)
          refine ⟨R, N, P, H, K, entered, processed, lastCaller, saved, last, next, outcome,
            ?_, lastPost, lastQuery, admitted, receiptHistory, receiptPosts, fragments, callbacks, outcomeShape, supported⟩
          intro er en ep eh ek
          rw [run_narrowed holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
            w w w w w w (R + er) (N + en) (P + ep) (H + eh) (K + ek)
            uv oldHandle newHandle scs oldValue value caller before after memos.query readAfter checked.core heap
            nextAction reading checking oldDecoded preparedAt raw encoded adaptedAt]
          have actual := ordinaryRun er en (P + ep) (H + eh) ek (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          rw [show SourcePruningEnumerationNativeOrdinary.run checkEmpty (R + er) (N + en) (P + ep) (H + eh)
            (K + ek) uv edgesOf
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
            after memos.query = _ from (by simpa only [query] using actual)]
        · rw [prefixRun]
          exact history
