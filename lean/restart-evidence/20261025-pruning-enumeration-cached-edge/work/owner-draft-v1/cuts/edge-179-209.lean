    have childrenAvailable : ∀ child ∈ edge.children, InternedProbeProvenance.Available heap child := by
      intro child member
      exact parentAvailable.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)
    have childrenClosed : ∀ child ∈ edge.children, child.free = [] := by
      exact MergedColdReaderClosed.node_children_closed heap ready.semantic.1.normal.facts
        parentEntry edges depth free parentAvailable parentClosed edge selected
    have childrenNonempty : ∀ child ∈ edge.children, child ≠ .empty := by
      intro child member emptyChild
      subst child
      exact (List.any_eq_false.mp
        (InternedLiveEdges.resident_live heap ready.semantic.1.normal.live
          (.node parentEntry edges depth free) parentAvailable.resident edge selected))
        .empty member (by rfl)
    let inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended) :=
      edge.children.zipIdx.map (fun indexed =>
        (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)))
    have stagedSame : inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1)) =
      edge.children.zipIdx.map (fun indexed =>
        (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries),
          SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
            (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)) indexed.1)) := by
      simp only [inputs, List.map_map]
      rfl
    obtain ⟨childrenResult, childrenAfter, childrenSuccess, completedPrefixSuccess, resultShape,
      afterCounter, afterAligned, afterRealized⟩ :=
      runStaged_complete inputs heap ready.semantic.1.normal.facts.coherent
        (suspendedState tries.length before) prefixRealized prefixAligned
        (by
          intro input member
