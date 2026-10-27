      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before.core → EnumerationReferences.IncomingAvoid held after.core) ∧
      (repeated = false → Frame before.core after.core ∧ after.expandable = before.expandable ∧
        after.waiting = before.waiting ∧ after.core.values[uv]? = some (.unenumerated (some handle) scs)) ∧
      (repeated = true → MergedOrdinaryHeight.recursiveBoundary value = true ∧
        after.core.values[uv]? = some (.unenumerated (some handle) []) ∧ after.expandable uv = false ∧
        after.waiting = EnumerationCanonicalWaiting.count roots (-1) scs before.waiting ∧
        ∃ (resolved : EnumerationState.State Symbol EnumGuard) (countFuel : Nat),
          Frame before.core resolved ∧
          Success (representative fuel uv) before.core uv resolved ∧
          recursionKey handle scs ∈ resolved.recursionAncestry uv ∧
          Success (setValue uv (.unenumerated (some handle) [])) resolved () after.core ∧
          ∀ extra, SourcePruningEnumerationNativeIndex.write heap (countFuel + extra) uv
            (.unenumerated (some handle) []) [] scs (EnumerationExpandableIndex.frame resolved before) = some after) := by
