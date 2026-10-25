theorem runStaged_exact
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (List (Fragments.Fragment Symbol))) :
    let staged := inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) input.2 input.1))
    Success (SourcePruningEnumerationEdgeTraversal.runStaged staged) before result after →
      SourcePruningEnumerationEdgeTraversal.runStaged staged before = [.ok (result, after)] := by
  dsimp only
  have childExact : ∀ (bucket : List EnumerationState.Suspended)
