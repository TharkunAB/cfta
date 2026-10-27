          formulas solver (bound + extra) caller memos before uv scs selectedEdges capturedMass inherited output := by
  induction selectedEdges generalizing seed inventory caller memos with
  | nil =>
      refine ⟨0, [], [], caller, inventory, memos, .complete [] [] caller memos.query,
        fun _ => rfl, Post.refl packet.context, packet, bounded, known, Nat.le_refl _, ?_, ?_, .inl rfl, ?_⟩
      · intro index receipt found
        cases found
      · intro output member
        cases member
      · intro extra output member
        cases member
  | cons edge rest ih =>
      obtain ⟨headBound, receipt, middleCaller, saved, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape, completedReceipt, callbackAdmission⟩ :=
        SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_with_history
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
          seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free edge packet ready stored decoded
          (selected edge List.mem_cons_self) incoming bounded known selectionMembers selectionLength
          capturedMass inherited initialMass inheritedLength reserved.head
      have laterGrowth := SourcePruningEnumerationFiniteReservation.stage_ge recursiveFuel
        (afterHook recursiveFuel seed capturedMass inherited) capturedMass inherited rest.length
      have headGrowth := SourcePruningEnumerationFiniteReservation.afterHead_le_step recursiveFuel seed capturedMass inherited
      have wholeFits : Fits (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).2 middleCaller.checked :=
        headFits.mono (headGrowth.1.trans laterGrowth.1)
      have wholeKnown : Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited (edge :: rest).length).1)
          middleCaller.checked.native.machine.heap :=
        fun key resident found => laterGrowth.2 (headGrowth.2 (headKnown key resident found))
      rcases shape with unsupported | ⟨outcome, advanced, callbackRun, resources, captured, rich⟩
      · obtain ⟨unhandled, _allowed, _projected⟩ := unsupported
        subst receipt
        refine ⟨headBound, [], [], middleCaller, middleInventory, middleMemos,
          .stopped [] [] (.edge (some .unhandled)), ?_, headPost,
          SourcePruningEnumerationRecursive.captured_post packet headPost, wholeFits, wholeKnown,
          by simp, ?_, ?_, .inr ⟨_, rfl, .inl rfl, .inl rfl⟩, ?_⟩
        · intro extra
          simp only [SourcePruningEnumerationNativeContinuations.run, headRun extra,
            SourcePruningEnumerationNativeBranches.advance]
        · intro index current found
          cases found
        · intro output member
          cases member
        · intro extra output member
          cases member
      · have receiptCertificate : ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited 0 receipt :=
          ⟨admitted, pending, history, cacheBounds, middleCaller, middleMemos.query, middleInventory, middleMemos,
            advanced, headPost, rfl, headFits, headKnown⟩
        have headHistories : ∀ extra output,
            output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
            InvocationHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
              formulas solver (headBound + extra) caller memos before uv scs (edge :: rest) capturedMass inherited output := by
          intro extra output member
          have completed : ∃ fragment actual queries after, receipt = .complete fragment actual queries after := by
            cases receipt with
            | complete fragment actual queries after => exact ⟨fragment, actual, queries, after, rfl⟩
            | unhandled => cases advanced
            | rejected actual queries after | stopped fragments observation candidate =>
                have empty := callbackRun extra
                rw [empty] at member
                cases member
          obtain ⟨fragment, actual, queries, after, same⟩ := completed
          subst receipt
