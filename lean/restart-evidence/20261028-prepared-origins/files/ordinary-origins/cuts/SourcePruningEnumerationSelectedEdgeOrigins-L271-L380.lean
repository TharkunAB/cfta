  have modelOrigins : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol) (terms : List (Language.Term Symbol)) (whole : Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient) edge.children terms →
      SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint
        (.node edge.entry.key.symbol terms) = true →
      (∀ sc ∈ scs, Suspended.Holds assignment (.node edge.entry.key.symbol terms) sc) →
      AssignmentOrigins whole before.core.counter assignment →
      Origin whole (.node edge.entry.key.symbol terms) →
      ∃ extended : Nat → Language.Term Symbol,
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended before.core ∧
        childResult = .complete fragments afterCaller savedQueries after ∧
        fragments.map (Fragments.fill extended) = terms ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          extended after.core ∧
        ResidualHolds
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          residual (.node edge.entry.key.symbol terms) ∧
        AssignmentOrigins whole after.core.counter extended := by
    intro ambient assignment terms whole satisfied accepted guardHolds inherited origins termOrigin
    obtain ⟨_validTries, projectionMeaning⟩ :=
      SourcePruningEnumerationEdgeProjectionLanguage.selected_projected_complete
        caller.checked.native.machine.heap parentEntry edges depth free edge
        initial.ready.semantic.ready initial.annotation_heap parentAvailable selected tries residual projected
    obtain ⟨equalities, residualHolds⟩ := (projectionMeaning formulas solver _).mp guardHolds
    obtain ⟨witnesses, ownSatisfied, freshAgree, freshHolds, ownOrigins⟩ :=
      fresh_classes_state_complete_origins
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        before.core safe.1 assignment satisfied whole (.node edge.entry.key.symbol terms) tries equalities origins termOrigin
    rw [← ownCore] at ownSatisfied ownOrigins
    have combinedHolds : ∀ sc ∈ scs ++ suspendedVars before.core.counter tries,
        Suspended.Holds witnesses (.node edge.entry.key.symbol terms) sc := by
      intro sc member
      rcases List.mem_append.mp member with old | fresh
      · exact EnumerationConstruction.holds_extension assignment witnesses before.core.counter
          freshAgree sc (bounded sc old) _ (inherited sc old)
      · exact freshHolds sc fresh
    have descended := suspended_descent_forward witnesses edge.entry.key.symbol terms
      (scs ++ suspendedVars before.core.counter tries) combinedHolds
    have indexed : ∀ (nodes : List Node) (values : List (Language.Term Symbol)),
        Language.All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient) nodes values →
        ∀ start,
          (∀ index child, values[index]? = some child →
            ∀ sc ∈ descendScs (start + index) (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) →
          Language.All₂ (fun indexed child =>
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient indexed.1 child ∧
            ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars before.core.counter tries),
              Suspended.Holds witnesses child sc) (nodes.zipIdx start) values := by
      intro nodes values related
      induction related with
      | nil => intro start _; exact .nil
      | cons head tail ih =>
          intro start holds
          simp only [List.zipIdx_cons]
          apply Language.All₂.cons
          · exact ⟨head, by simpa only [Nat.add_zero] using holds 0 _ rfl⟩
          · apply ih (start + 1)
            intro index child found
            have evidence := holds (index + 1) child found
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using evidence
    have indexedModels := indexed edge.children terms accepted 0 (by simpa only [Nat.zero_add] using descended)
    have inputModels : Language.All₂ (fun input term =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds witnesses term sc) inputs terms := by
      have mapped := EnumerationSemantics.all₂_map_both
        (fun indexed : Node × Nat => (indexed.1,
          descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.core.counter tries)))
        id
        (fun indexed child =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient indexed.1 child ∧
          ∀ sc ∈ descendScs indexed.2 (scs ++ suspendedVars before.core.counter tries),
            Suspended.Holds witnesses child sc)
        (fun input term =>
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds witnesses term sc)
        (fun _ _ evidence => ⟨evidence.1, by
          simpa only [id_eq, descendScs, EqualityTrie.descendScs, List.map_append, List.filter_append]
            using evidence.2⟩)
        edge.children.zipIdx terms indexedModels
      simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.map_id] using mapped
    obtain ⟨extended, childAgree, _ownOriginalSatisfied, completed, filled, afterSatisfied, afterOrigins⟩ :=
      childrenOrigins ambient
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        witnesses terms whole ownSatisfied inputModels ownOrigins
        (fun child member => origin_child whole edge.entry.key.symbol terms child termOrigin member)
    have agree : ∀ uv < before.core.counter, extended uv = assignment uv := by
      intro uv inside
      exact (childAgree uv (by omega)).trans (freshAgree uv inside)
    have originalSatisfied := (state_assignment_congr
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
