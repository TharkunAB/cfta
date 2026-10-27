/-- The selected own prefix preserves every optional action and both cached indexes. -/
theorem prepare_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint) :
    PreparedRelated (prepare heap scs edge flat)
      (SourcePruningEnumerationCachedOwn.prepare heap scs edge earlier) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, PreparedRelated]
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        obtain ⟨own, next, after, actual, oldActual, states⟩ := suspendMany_related heap tries related
        have staged : Language.All₂ StageRelated
            (edge.children.zipIdx.map fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourceFlatPruningShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
            (edge.children.zipIdx.map fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)) := by
          induction edge.children.zipIdx with
          | nil => exact .nil
          | cons indexed rest ih =>
              exact .cons ⟨rfl, rfl, SourceFlatPruningShallowChild.prepareChild_related _ _⟩ ih
        simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, actual, oldActual, Option.map_some, PreparedRelated]
        exact .cons ⟨rfl, staged, rfl, states⟩ .nil
  · simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, PreparedRelated]
    exact .nil
