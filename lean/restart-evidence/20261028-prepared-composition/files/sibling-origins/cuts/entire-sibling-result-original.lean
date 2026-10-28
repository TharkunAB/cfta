    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      ∀ extra,
        let work := bound + extra
        let hook := continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
          graph templates stop order work metadata uv
        ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint), selectedEdges[index]? = some chosen →
          (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
            SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol)
            (whole : Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient chosen (assignment uv) →
            AssignmentOrigins whole before.core.counter assignment →
            ∃ (eventIndex : Nat) (eventEdge : EdgeValue Symbol Constraint)
              (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
              (prefixReceipts : List (Receipt (bits + 2))) (prefixOutputs : List (Output (bits + 2) Typing))
              (fragment : Fragment) (branchCaller : Caller (bits + 2)) (branchQueries : Queries)
              (afterCache : Cached) (branchInventory : Inventory) (branchMemos : Memos),
              eventIndex ≤ index ∧ selectedEdges[eventIndex]? = some eventEdge ∧
              prefixReceipts.length = eventIndex ∧
              Post formulas solver headInventory caller headCaller headMemos ∧
              Packet formulas solver headInventory headCaller headMemos metadata before ∧
              Fits (stage recursiveFuel seed capturedMass inherited eventIndex).2 headCaller.checked ∧
              Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited eventIndex).1)
                headCaller.checked.native.machine.heap ∧
              SourcePruningEnumerationPreparedReservation.HeadReserved bits recursiveFuel
                (stage recursiveFuel seed capturedMass inherited eventIndex) capturedMass inherited ∧
              SourcePruningEnumerationNativeContinuations.run hook checkEmpty work work work work work
                uv scs before (selectedEdges.take eventIndex) caller memos.query =
                .complete prefixReceipts prefixOutputs headCaller headMemos.query ∧
              Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
              branchMemos.query = branchQueries ∧
              SourcePruningEnumerationCapturedEdge.run checkEmpty work work work work work uv scs
                eventEdge headCaller before headMemos.query =
                some (.complete fragment branchCaller branchQueries afterCache) ∧
              SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty work work work work work
                uv scs before selectedEdges caller memos.query fragment branchCaller branchQueries afterCache ∧
              ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited eventIndex
                (.complete fragment branchCaller branchQueries afterCache) ∧
              ((eventIndex = index ∧ eventEdge = chosen ∧
                  ∃ extended : Nat → Language.Term Symbol,
                    (∀ old < before.core.counter, extended old = assignment old) ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient caller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended before.core ∧
                    Fragments.fill extended fragment = assignment uv ∧
                    Satisfies
                      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                        ambient branchCaller.checked.native.machine.heap)
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      extended afterCache.core ∧
                    AssignmentOrigins whole afterCache.core.counter extended) ∨
                (eventIndex < index ∧
                  ∃ (hookOutputs : List (Output (bits + 2) Typing)) (reason : Failure (bits + 2) Typing)
                    (reached : Option (Caller (bits + 2) × Queries)),
                    hook fragment branchCaller branchQueries afterCache = .stopped hookOutputs reason reached ∧
                    result = .stopped prefixReceipts (prefixOutputs ++ hookOutputs)
                      (.continuation (.complete fragment branchCaller branchQueries afterCache) reason reached) ∧
                    SourcePruningEnumerationPreparedRecursive.OutcomeResources formulas solver caller
                      (stage recursiveFuel seed capturedMass inherited (eventIndex + 1))
                      (.stopped hookOutputs reason reached)))