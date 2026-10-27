    List (EdgeValue Symbol Constraint) → Caller width → Queries →
      Fragment → Caller width → Queries → Cached → Prop where
  /-- The first edge completes at the recorded hook input. -/
  | here {edge rest caller queries fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some (.complete fragment reached saved after)) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after
  /-- A completed hook supplies the actual native endpoint of the suffix. -/
  | completed {edge rest caller queries first headCaller headQueries headCache outputs middleCaller middleQueries
        fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some (.complete first headCaller headQueries headCache))
      (continued : hook first headCaller headQueries headCache = .complete outputs middleCaller middleQueries)
      (tail : Invocation hook checkEmpty r n p h k target scs before rest middleCaller middleQueries
        fragment reached saved after) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after
  /-- A handled receipt without a completed fragment advances only native state. -/
  | other {edge rest caller queries receipt middleCaller middleQueries fragment reached saved after}
      (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
        some receipt)
      (notComplete : match receipt with | .complete .. => False | _ => True)
      (advanced : SourcePruningEnumerationNativeBranches.advance receipt = some (middleCaller, middleQueries))
      (tail : Invocation hook checkEmpty r n p h k target scs before rest middleCaller middleQueries
        fragment reached saved after) :
      Invocation hook checkEmpty r n p h k target scs before (edge :: rest) caller queries
        fragment reached saved after

/-- Every emitted scan output comes from a literal hook invocation on its actual path. -/
