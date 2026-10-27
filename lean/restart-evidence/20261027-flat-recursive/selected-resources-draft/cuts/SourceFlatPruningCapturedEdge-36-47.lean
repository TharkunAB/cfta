theorem run_completed (checkEmpty : Bool) (r nativeFuel p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (flat : Cached)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) (queries : Queries)
    (earlier : SourcePruningEnumerationSelectedEdge.Result width)
    (selected : SourceFlatPruningSelectedEdge.ResultRelated
      (SourceFlatPruningSelectedEdge.run checkEmpty nativeFuel p h scs edge caller flat queries)
      (SourcePruningEnumerationSelectedEdge.run checkEmpty r nativeFuel p h k scs edge caller before queries))
    (completed : SourcePruningEnumerationCapturedEdge.run checkEmpty r nativeFuel p h k target
      scs edge caller before queries = some earlier) :
    ∃ next, run checkEmpty nativeFuel p h target scs edge caller flat queries = some next ∧
      SourceFlatPruningSelectedEdge.ResultRelated next earlier := by
