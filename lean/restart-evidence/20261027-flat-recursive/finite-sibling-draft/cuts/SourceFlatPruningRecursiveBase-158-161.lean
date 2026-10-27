theorem finish_related (uv : Nat) (flat : Fold) (earlier : OldFold)
    (related : SourceFlatPruningNativeContinuations.ResultRelated
      OutputRelated FailureRelated flat earlier) :
    ResultRelated (finish uv flat) (SourcePruningEnumerationRecursive.finish uv earlier) := by
