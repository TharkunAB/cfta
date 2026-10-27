              intro index chosen found supported ambient assignment satisfied accepted
              let w := bound + extra
              let hook : Fragment → Caller (bits + 2) → Queries → Cached →
                  HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := continueWith
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                graph templates stop order w metadata uv
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      hook fragment actual queries after = .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              cases index with
              | zero =>
                  have chosenSame : edge = chosen := Option.some.inj found
                  subst chosen
                  obtain ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
                    headAccepting ambient assignment satisfied accepted
                  have observed : SourcePruningEnumerationCapturedEdge.run checkEmpty w w w w w
                      uv scs edge caller before memos.query =
                      some (.complete fragment middleCaller saved afterCache) := by
                    rw [completed] at first
                    exact first
