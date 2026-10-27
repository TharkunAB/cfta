    · intro held old different expanded
      apply origin held old
      rw [core] at expanded
      simpa only [List.getElem?_set_ne (Ne.symm different)] using expanded
    · intro held different inside root separate
      have oldFrame := protects held inside root separate
      apply oldFrame.trans
      refine ⟨?_, ?_, ?_⟩
      · rw [core]
        exact List.getElem?_set_ne (Ne.symm different)
      · rw [core]
        exact oldFrame.root
      · rw [core]
        exact fun _ => Iff.rfl
    · intro history incoming
      have written := EnumerationReferences.setValue_pending uv fragment middle.core
        {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
        (pendingHistory history) (incomingHistory uv ready.inside ready.root avoids incoming)
        ((EnumerationDriver.modify_success _ _ _).mpr rfl)
      rw [core]
      exact written
