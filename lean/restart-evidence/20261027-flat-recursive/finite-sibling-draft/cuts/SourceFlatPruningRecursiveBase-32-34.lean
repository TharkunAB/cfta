theorem advance_related (flat : Receipt width) (earlier : OldReceipt width)
    (related : SourceFlatPruningSelectedEdge.ResultRelated flat earlier) :
    SourceFlatPruningNativeBranches.advance flat = SourcePruningEnumerationNativeBranches.advance earlier := by
