/-- Match the actual selected-edge prefix and retain both native indexes. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) (roots : Nat → Nat)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    if arityAllows edge.children.length scs then
      match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none => prepare heap scs edge before = none ∧
          SourcePruningEnumerationEdgePrefix.prepare scs edge = none
      | some (tries, residual) =>
          let own : List EnumerationState.Suspended := suspendedVars before.core.counter tries
          let staged := edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
          ∃ (action : EnumerateM Symbol Constraint (Symbol ×
              List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended ×
                Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint))
            (after : EnumerationExpandableIndex.Cached Symbol Constraint),
            SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
            prepare heap scs edge before = some [((edge.entry.key.symbol, staged, residual), after)] ∧
            ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol, staged, residual), after.core)] ∧
            after.core = suspendedState tries.length before.core ∧
            after.core.counter = before.core.counter + tries.length ∧
            after.core.counter = after.core.values.length ∧
            after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
