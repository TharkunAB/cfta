    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (earlierEdges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries)
    {processed : List (Receipt width)} {outputs : List Output}
    {afterCaller : Caller width} {afterQueries : Queries}
    (completed : run hook checkEmpty r n p h k target scs before earlierEdges caller queries =
      .complete processed outputs afterCaller afterQueries)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge
      afterCaller before afterQueries = some (.complete fragment reached saved after)) :
    Invocation hook checkEmpty r n p h k target scs before (earlierEdges ++ edge :: rest)
      caller queries fragment reached saved after := by
  induction earlierEdges generalizing caller queries processed outputs afterCaller afterQueries with
  | nil =>
      simp only [run, Result.complete.injEq] at completed
      obtain ⟨_receipts, _outputs, rfl, rfl⟩ := completed
      exact .here observed
  | cons first earlierEdges ih =>
      cases captured : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs
          first caller before queries with
      | none => simp only [run, captured] at completed; cases completed
      | some receipt =>
          cases receipt with
          | unhandled =>
              simp only [run, captured, SourcePruningEnumerationNativeBranches.advance] at completed; cases completed
          | complete firstFragment headCaller headQueries headCache =>
              cases hooked : hook firstFragment headCaller headQueries headCache with
