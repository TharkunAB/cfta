            obtain ⟨tailBound, tailReceipts⟩ :=
              ih (afterHook recursiveFuel seed capturedMass inherited) hookInventory hookCaller hookMemos hookCaptured
                (lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)
                (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) hookFits hookKnown reserved.tail
            let bound := headBound + tailBound
            refine ⟨bound, ?_⟩
            intro extra fragment reached saved after invocation
            let w := bound + extra
            have hl : headBound ≤ w := by dsimp [w, bound]; omega
            have tl : tailBound ≤ w := by dsimp [w, bound]; omega
            have first := headRun (w - headBound)
            rw [Nat.add_sub_of_le hl] at first
            have hooked := callbackRun (w - headBound)
            rw [Nat.add_sub_of_le hl] at hooked
            have tailAt := tailReceipts (w - tailBound) fragment reached saved after
            rw [Nat.add_sub_of_le tl, hookQuery] at tailAt
            cases invocation with
            | here observed =>
                have same : receipt = .complete fragment reached saved after :=
                  Option.some.inj (first.symm.trans observed)
                exact ⟨edge, List.mem_cons_self, seed, inventory, caller, memos, headBound,
                  middleInventory, middleMemos, Post.refl packet.context, observed,
                  completedReceipt fragment reached saved after same,
                  callbackAdmission fragment reached saved after same⟩
            | completed observed continued tail =>
                have same := Option.some.inj (first.symm.trans observed)
                rw [same] at hooked
                obtain ⟨_outputs, rfl, rfl⟩ :=
                  SourcePruningEnumerationNativeContinuations.HookResult.complete.inj (hooked.symm.trans continued)
                obtain ⟨chosen, member, headSeed, headInventory, headCaller, headMemos, localBound,
                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate, admission⟩ := tailAt tail
                exact ⟨chosen, List.mem_cons_of_mem _ member, headSeed, headInventory, headCaller, headMemos,
                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead,
                  certificate, admission⟩
            | other observed notComplete actualAdvance tail =>
                have same := Option.some.inj (first.symm.trans observed)
                have noncomplete : (match (generalizing := false) receipt with | .complete .. => False | _ => True) := by
                  cases same
                  cases receipt <;> exact notComplete
                have canonicalAdvance : advance receipt = some (hookCaller, hookQueries) := by
                  cases receipt with
                  | complete _ _ _ _ => cases noncomplete
                  | unhandled => cases advanced
                  | rejected actual queries cache | stopped fragments observation candidate =>
                      obtain ⟨_outputs, actualSame, queriesSame⟩ :=
                        SourcePruningEnumerationNativeContinuations.HookResult.complete.inj hooked
                      rw [actualSame, queriesSame]
                      exact advanced
                rw [← same] at actualAdvance
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (canonicalAdvance.symm.trans actualAdvance))
                obtain ⟨chosen, member, headSeed, headInventory, headCaller, headMemos, localBound,
                  returnedInventory, returnedMemos, prefixPost, observedHead, certificate, admission⟩ := tailAt tail
                exact ⟨chosen, List.mem_cons_of_mem _ member, headSeed, headInventory, headCaller, headMemos,
                  localBound, returnedInventory, returnedMemos, hookPost.trans prefixPost, observedHead,
