      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment afterCache
        level frontier post.context admitted history pending ordered packet.bounded
      have allocated : FragmentBound afterCache.core.counter fragment := admitted.2.2.1
      obtain ⟨callbackFuel, recorded, callbackCore, callbackOutcome, returned, equivalence, models⟩ :=
        callback_finite_complete_resources_models holeKey fits admits formulas solver next graph templates metadata
          uv fragment reached final afterCache checkEmpty edgesOf stop order recursiveFuel seed ceiling
          current allocated bounded known selectionMembers selectionLength mass reserved
      obtain ⟨callbackPacket, stable, framed, types, holes, typing, callback, callbackRunning, callbackResources⟩ := returned
      have sameOutcome : callbackOutcome = outcome := by
        have oldRun := receiptRunning callbackFuel
        have modelRun := callbackRunning receiptFuel
        rw [Nat.add_comm callbackFuel receiptFuel] at modelRun
        exact modelRun.symm.trans oldRun
      subst callbackOutcome
      refine ⟨receiptFuel + callbackFuel, outcome, ⟨?_, receiptResources⟩,
        rfl, rfl, recorded, callbackCore, current, allocated,
        ⟨callbackPacket, stable, framed, types, holes, typing, ?_, ?_, callbackResources⟩,
        equivalence, ?_⟩
      · intro extra
        have actual := receiptRunning (callbackFuel + extra)
        rw [← Nat.add_assoc] at actual
        exact actual
      · intro extra
        have actual := callback (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual
      · intro extra
        have actual := callbackRunning (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual
      · intro language meaning assignment satisfied filled refuted avoids encoded
        obtain ⟨afterSatisfied, notRejected, pendingRefutes, restarting⟩ :=
          models language meaning assignment satisfied filled refuted avoids encoded
        refine ⟨afterSatisfied, notRejected, pendingRefutes, ?_⟩
        intro extra
        have actual := restarting (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
