theorem split_event
    (checkEmpty : Bool) (r n p h k : Nat)
    (consumed suffix : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
    (caller afterCaller : Caller width) (before after : Cached) (queries afterQueries : Queries)
    (fragments : List Fragment)
    (trace : Trace checkEmpty r n p h k (consumed ++ (value, bucket) :: suffix)
      caller before queries fragments afterCaller after afterQueries) :
    ∃ (prefixFragments : List Fragment) (fragment : Fragment) (suffixFragments : List Fragment)
      (eventCaller preparedCaller : Caller width) (eventBefore prepared : Cached)
      (eventQueries preparedQueries : Queries) (outer : EnumerationState.State Symbol Constraint)
      (waiting : EnumerationWaitingIndex.Waiting),
      fragments = prefixFragments ++ fragment :: suffixFragments ∧
      Trace checkEmpty r n p h k consumed caller before queries
        prefixFragments eventCaller eventBefore eventQueries ∧
      SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket value
        eventCaller eventBefore eventQueries =
        ((.ok (some [.ok (fragment, prepared.core)]), preparedCaller, preparedQueries, outer, waiting),
          some prepared) ∧
      Trace checkEmpty r n p h k suffix preparedCaller prepared preparedQueries
        suffixFragments afterCaller after afterQueries := by
  induction consumed generalizing caller before queries fragments with
  | nil =>
      cases trace with
      | cons head tail =>
          exact ⟨[], _, _, _, _, _, _, _, _, _, _, rfl, .nil _ _ _, head, tail⟩
  | cons input consumed ih =>
      cases trace with
      | cons head tail =>
          obtain ⟨prefixFragments, fragment, suffixFragments, eventCaller, preparedCaller,
            eventBefore, prepared, eventQueries, preparedQueries, outer, waiting,
            fragmentSplit, prefixTrace, event, suffixTrace⟩ := ih _ _ _ _ tail
          refine ⟨_ :: prefixFragments, fragment, suffixFragments, eventCaller, preparedCaller,
            eventBefore, prepared, eventQueries, preparedQueries, outer, waiting,
            ?_, .cons head prefixTrace, event, suffixTrace⟩
          simpa only [List.cons_append] using congrArg (List.cons _) fragmentSplit

/-- A nonterminal successful row comes from the same cached preparation. -/
theorem nonterminal_child_row
