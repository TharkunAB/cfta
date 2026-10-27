            obtain ⟨tailBound, processed, outputs, afterCaller, next, final, tailResult,
              tailRun, tailPost, tailCaptured, tailFits, tailKnown, tailLength, tailReceipts, tailOutputs, tailShape⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail
            let bound := headBound + tailBound
            let result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
              match (generalizing := false) tailResult with
              | .complete receipts later actual queries => .complete (receipt :: receipts) (headOutputs ++ later) actual queries
              | .stopped receipts later current => .stopped (receipt :: receipts) (headOutputs ++ later) current
            refine ⟨bound, receipt :: processed, headOutputs ++ outputs, afterCaller, next, final, result,
              ?_, hookPost.trans tailPost, tailCaptured, tailFits, tailKnown, by simpa only [List.length_cons] using Nat.add_le_add_right tailLength 1,
              ?_, ?_, ?_⟩
            · intro extra
              let w := bound + extra
              have hl : headBound ≤ w := by dsimp [w, bound]; omega
              have tl : tailBound ≤ w := by dsimp [w, bound]; omega
              have first := headRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at first
              have hooked := callbackRun (w - headBound)
              rw [Nat.add_sub_of_le hl] at hooked
              have continued : match (generalizing := false) receipt with
                  | .complete fragment actual queries after =>
                      continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                        graph templates stop order w metadata uv fragment actual queries after =
                        .complete headOutputs hookCaller hookQueries
                  | _ => advance receipt = some (hookCaller, hookQueries) ∧ headOutputs = [] := by
                cases receipt with
                | complete fragment actual queries after => exact hooked
                | unhandled => cases advanced
                | rejected actual queries after | stopped fragments observation candidate =>
                    obtain ⟨empty, actual, queries⟩ :=
                      SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                    exact ⟨by rw [actual, queries]; exact advanced, empty⟩
              have running := SourcePruningEnumerationNativeContinuations.continued_head
                (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order w recursiveFuel)
                  graph templates stop order w metadata uv)
                checkEmpty w w w w w uv scs before edge rest caller hookCaller memos.query hookQueries
                receipt headOutputs first (by cases receipt <;> exact continued)
              have later := tailRun (w - tailBound)
              rw [Nat.add_sub_of_le tl, hookQuery] at later
              rw [later] at running
              cases tailResult <;> exact running
            · intro index current found
              cases index with
              | zero =>
                  have same : receipt = current := Option.some.inj found
                  subst current
                  exact receiptCertificate
              | succ index =>
                  have member : processed[index]? = some current := by simpa only [List.getElem?_cons_succ] using found
                  exact (tailReceipts index current member).prepend hookPost
            · intro output member
              rcases List.mem_append.mp member with first | later
              · exact ⟨0, by simp, headOutputsValid output first⟩
              · obtain ⟨index, inside, certificate⟩ := tailOutputs output later
                exact ⟨index + 1, by simpa only [List.length_cons] using Nat.add_lt_add_right inside 1,
                  certificate.prepend hookPost⟩
            · rcases tailShape with completed | ⟨current, stopped, observed, certificate⟩
              · exact .inl (by simp only [result, completed])
              · exact .inr ⟨current, by simp only [result, stopped], observed,
                  certificate.prepend hookPost headOutputs⟩
        | stopped headOutputs reason reached =>
            have currentResources := resources
            obtain ⟨afterCaller, next, final, post, returnedFits, returnedKnown, observed, outputsValid⟩ := resources
