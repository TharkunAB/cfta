theorem related_output_member
    (flat : SourceFlatPruningNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width)
    (related : ResultRelated flat earlier) :
    ∀ output ∈ flatOutputs flat, ∃ original ∈ oldOutputs earlier, OutputRelated output original := by
