            · intro extra
              dsimp only
              intro index chosen found supported ambient assignment satisfied accepted
              let w := headBound + extra
              have observed := headRun extra
              have invoked : SourcePruningEnumerationHookInvocation.Invocation
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before (edge :: rest) caller memos.query
                  fragment actual queries after := .here observed
              have inputPrefix : SourcePruningEnumerationNativeContinuations.run
                  (continueWith
                    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                    graph templates stop order w metadata uv)
                  checkEmpty w w w w w uv scs before ((edge :: rest).take 0) caller memos.query =
                  .complete [] [] caller memos.query := rfl
              have actualSame : actual = middleCaller ∧ queries = saved := by
                simp only [SourcePruningEnumerationNativeBranches.advance, Option.some.injEq, Prod.mk.injEq] at advanced
                exact ⟨advanced.1, advanced.2.trans headQueries⟩
              have localPost : Post formulas solver middleInventory caller actual middleMemos := by
                simpa only [actualSame.1] using headPost
              have localQuery : middleMemos.query = queries := headQueries.trans actualSame.2.symm
              refine ⟨0, edge, inventory, caller, memos, [], [], fragment, actual, queries, after,
                middleInventory, middleMemos, by omega, rfl, rfl, Post.refl packet.context,
                packet, bounded, known, reserved.head, inputPrefix, localPost, localQuery,
                observed, invoked, receiptCertificate, ?_⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, chosenFragment, chosenCache, agree, originalSatisfied,
                    completed, filled, afterSatisfied⟩ := headAccepting ambient assignment satisfied accepted
                  have equality := SourcePruningEnumerationSelectedEdge.Result.complete.inj completed
                  obtain ⟨rfl, _sameCaller, _sameQueries, rfl⟩ := equality
                  exact .inl ⟨rfl, rfl, extended, agree, originalSatisfied, filled, by
                    simpa only [actualSame.1] using afterSatisfied⟩
              | succ index =>
                  refine .inr ⟨by omega, headOutputs, reason, reached, callbackRun extra, ?_, ?_⟩
                  · rfl
                  · exact currentResources
