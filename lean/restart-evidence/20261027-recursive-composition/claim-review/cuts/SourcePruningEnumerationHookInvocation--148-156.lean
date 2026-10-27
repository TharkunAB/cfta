theorem Invocation.selected
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {before : Cached}
    {edges : List (EdgeValue Symbol Constraint)} {caller reached : Caller width} {queries saved : Queries}
    {fragment : Fragment} {after : Cached}
    (invocation : Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after) :
    ∃ edge ∈ edges, ∃ headCaller headQueries,
      SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge headCaller before headQueries =
        some (.complete fragment reached saved after) := by
