abbrev ReceiptsRelated (flat : List (Receipt width))
    (earlier : List (SourcePruningEnumerationSelectedEdge.Result width)) : Prop :=
  OrderedRelated SourceFlatPruningSelectedEdge.ResultRelated flat earlier

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
