theorem prepare_exact
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (Fragments.Fragment Symbol))
    (prepared : SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action)
    (observed : Success action before result after) :
    action before = [.ok (result, after)] := by
  by_cases allowed : arityAllows edge.children.length scs = true
  ·
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
