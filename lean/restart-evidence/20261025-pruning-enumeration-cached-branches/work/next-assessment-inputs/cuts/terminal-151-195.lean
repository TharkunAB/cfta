      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extraRepresentative) (n + extraNative) P H first rest waiting
          beforeCaller before incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, moved)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (foldRaw = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRaw = [.ok ((), folded)] →
        ∃ (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read afterWrite : EnumerationState.State Symbol EnumGuard) (replacement : Node) (handle : Nat),
          outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), afterWrite)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), afterWrite)] ∧
          afterWrite.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid afterWrite ∧ PendingRealized afterCaller.checked.native.machine.heap afterWrite ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            afterWrite.values
            (EnumerationCanonicalWaiting.count (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
              1 incomingScs moved) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, afterWrite)]) ∧
          FragmentBound afterWrite.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : SourceEqualityNativeDemand.State width),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧
              next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old
                foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term))) := by
