theorem correct_of_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (roots : Nat → Nat)
    (paths : EnumerationSchedule.Roots earlier.core.representatives roots)
    (aligned : earlier.core.counter = earlier.core.values.length)
    (flags : ∀ uv, SourcePruningEnumerationNativeIndex.candidate heap
      ((earlier.core.values[uv]?).getD .eliminated) = some (earlier.expandable uv))
    (waiting : EnumerationCanonicalWaiting.Correct roots earlier.core.values earlier.waiting) :
    Correct heap flat := by
