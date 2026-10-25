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
