          ∀ extra,
            let work := bound + extra
            let hook := continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order work recursiveFuel)
              graph templates stop order work metadata uv
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
                      (.stopped hookOutputs reason reached))) := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result, retained⟩ :=
    alternatives_finite_complete_resources_origins
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges
      depth free packet ready stored parentAvailable parentClosed
      (fun edge member => selectedRows.mem_iff.mp member) incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, processed, outputs, afterCaller, next, final, result, retained, ?_⟩
  intro ambient assignment whole satisfied parentAccepted origins
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap packet.context.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free parentAvailable selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  obtain ⟨_running, _post, _captured, _fits, _known, _length, _receipts, _outputs, _shape, accepting⟩ := retained
  refine ⟨index, chosen, found, accepted, ?_⟩
  intro extra
  exact accepting extra index chosen found prefixSupported ambient assignment whole satisfied accepted origins

end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources
