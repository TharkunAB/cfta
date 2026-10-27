                have hooked := callbackRun (w - headBound)
                rw [Nat.add_sub_of_le hl] at hooked
                rw [hookQuery] at invocation
                have origin : SourcePruningEnumerationHookInvocation.Invocation
                    (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                      graph templates stop order w metadata uv)
                    checkEmpty w w w w w uv scs before (edge :: rest) caller memos.query
                      fragment reached returnedMemos.query after := by
                  cases receipt with
                  | complete firstFragment firstCaller firstQueries firstCache =>
                      exact .completed first hooked invocation
                  | unhandled => cases advanced
                  | rejected actual queries cache | stopped fragments observation candidate =>
                      obtain ⟨_empty, actualSame, queriesSame⟩ :=
                        SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                      exact .other first trivial (by
                        rw [actualSame, queriesSame]
                        exact advanced) invocation
                exact ⟨chosen, List.mem_cons_of_mem edge chosenMember, localSeed, localInventory, localCaller,
                  localMemos, localBound, fragment, reached, after, returnedInventory, returnedMemos, recorded,
                  callbackCore, hookPost.trans prefixPost, origin, actualRun, certificate, originalAdmission,
                  callback, returnedAdmission, recursiveHistory⟩
        | stopped headOutputs reason reached =>
            have currentResources := resources
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := resources
            have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
              cases receipt with
              | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
              | unhandled => cases advanced
              | rejected actual queries after | stopped fragments observation candidate =>
                  have impossible := callbackRun 0
                  cases impossible
            obtain ⟨fragment, actual, queries, after, same⟩ := completed
            subst receipt
            refine ⟨headBound, [], headOutputs, afterCaller, next, final,
              .stopped [] headOutputs (.continuation (.complete fragment actual queries after) reason reached),
              ?_, post, SourcePruningEnumerationRecursive.captured_post packet post,
              returnedFits.mono laterGrowth.1, ?_, by simp, ?_, ?_, ?_, ?_⟩
            · intro extra
              simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra, callbackRun extra]
            · intro key resident found
              exact laterGrowth.2 (returnedKnown key resident found)
            · intro index current found
              cases found
            · intro output member
              exact ⟨0, by simp, outputsValid output member⟩
            · exact .inr ⟨_, rfl, observed, .inr ⟨_, reason, reached, headOutputs, [], rfl, rfl,
                receiptCertificate, currentResources⟩⟩
            · intro extra output member
              exact headHistories extra output member
