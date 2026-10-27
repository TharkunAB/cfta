/-- Allocate own classes and capture the existing ordered child actions. -/
noncomputable def prepare
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Option (List ((Symbol ×
      List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended ×
        Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint)) :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => none
    | some (tries, residual) =>
        (suspendMany heap tries before).map fun result =>
          [((edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 result.1,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 result.1) indexed.1)),
            residual), result.2)]
