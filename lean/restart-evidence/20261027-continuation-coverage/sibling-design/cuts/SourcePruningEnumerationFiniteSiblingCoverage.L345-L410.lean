                      caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                      assignment realized hookPost.effects.keeps).mpr satisfied
                  have later := tailAccepting (headBound + extra) index chosen tailFound tailSupported
                    ambient assignment middleSatisfied accepted
                  have common : tailBound + (headBound + extra) = w := by dsimp [w, bound]; omega
                  rw [common] at later
                  obtain ⟨eventIndex, eventEdge, headInventory, headCaller, headMemos,
                    prefixReceipts, prefixOutputs, fragment, branchCaller, branchQueries, afterCache,
                    branchInventory, branchMemos, within, atIndex, prefixLength, inputPost, inputPacket,
                    inputFits, inputKnown, inputReserved, prefixRun, branchPost, branchQuery, observed,
                    _invocation, certificate, terminal⟩ := later
                  have liftedPrefix : SourcePruningEnumerationNativeContinuations.run hook
                      checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                      caller memos.query = .complete (receipt :: prefixReceipts)
                        (headOutputs ++ prefixOutputs) headCaller headMemos.query := by
                    have running := SourcePruningEnumerationNativeContinuations.continued_head hook
                      checkEmpty w w w w w uv scs before edge (rest.take eventIndex) caller hookCaller
                      memos.query hookQueries receipt headOutputs first (by cases receipt <;> exact continued)
                    rw [←hookQuery, prefixRun] at running
                    simpa only [List.take_succ_cons] using running
                  have newAt : (edge :: rest)[eventIndex + 1]? = some eventEdge := by
                    simpa only [List.getElem?_cons_succ] using atIndex
                  have split : (edge :: rest) = (edge :: rest).take (eventIndex + 1) ++
                      eventEdge :: (edge :: rest).drop (eventIndex + 2) := by
                    obtain ⟨inside, selectedAt⟩ := List.getElem?_eq_some_iff.mp newAt
                    have dropped := List.drop_eq_getElem_cons inside
                    rw [selectedAt] at dropped
                    rw [←dropped]
                    exact (List.take_append_drop (eventIndex + 1) (edge :: rest)).symm
                  have actualInvocation := SourcePruningEnumerationNativeContinuations.complete_prefix_invocation
                    hook checkEmpty w w w w w uv scs before ((edge :: rest).take (eventIndex + 1))
                    caller memos.query liftedPrefix eventEdge ((edge :: rest).drop (eventIndex + 2))
                    fragment branchCaller branchQueries afterCache observed
                  rw [←split] at actualInvocation
                  refine ⟨eventIndex + 1, eventEdge, headInventory, headCaller, headMemos,
                    receipt :: prefixReceipts, headOutputs ++ prefixOutputs, fragment, branchCaller,
                    branchQueries, afterCache, branchInventory, branchMemos, by omega, newAt,
                    by simpa only [List.length_cons] using congrArg (fun n => n + 1) prefixLength,
                    hookPost.trans inputPost, inputPacket, ?_, ?_, ?_, liftedPrefix,
                    branchPost, branchQuery, observed, actualInvocation, certificate.prepend hookPost, ?_⟩
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputFits
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputKnown
                  · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using inputReserved
                  · rcases terminal with ⟨sameIndex, sameEdge, extended, agree, oldSatisfied, filled, afterSatisfied⟩ |
                        ⟨earlier, hookOutputs, reason, endpoint, stoppedHook, stoppedResult, stoppedResources⟩
                    · have originalSatisfied :=
                        (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                          (SourceEqualityPCSGuard.holds formulas solver) ambient
                          caller.checked.native.machine.heap hookCaller.checked.native.machine.heap before.core
                          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                          extended realized hookPost.effects.keeps).mp oldSatisfied
                      exact .inl ⟨by omega, sameEdge, extended, agree, originalSatisfied, filled, afterSatisfied⟩
                    · refine .inr ⟨by omega, hookOutputs, reason, endpoint, stoppedHook, ?_, ?_⟩
                      · simp only [result, stoppedResult, List.append_assoc]
                      · simpa only [SourcePruningEnumerationFiniteReservation.stage_succ] using
                          stoppedResources.post hookPost
        | stopped headOutputs reason reached =>
            have currentResources := resources
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := resources
            have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
              cases receipt with
              | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
              | unhandled => cases advanced
              | rejected actual queries after | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
