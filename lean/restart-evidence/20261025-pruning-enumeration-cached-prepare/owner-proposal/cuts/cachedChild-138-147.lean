      after.core.counter = before.core.counter + 1 ∧ after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      after.expandable =
        (fun slot => if slot = before.core.counter then true else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots 1 scs before.waiting ∧
      FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter) := by
