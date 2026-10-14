import MicroCFTA.SourceRecursiveIntersectionInputLanguage

/-!
# Complete copied language of original physical inputs

Every independent finite input derivation is accepted by copied original
syntax. Free environments contain derivations through the stated rank.
Least recursive binders contain each finite unfolding by rank induction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule Language

/-- Copied original physical syntax contains all independently derived terms through each finite rank. -/
theorem Original.copy_complete (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) : ∀ rank environment, CompleteEnvironment state holds value rank environment →
      ∀ term, InputDerivation (view state holds) (inputOf value) rank term → meaning environment (shape holds value) term := by
  induction original with
  | empty =>
      intro rank environment complete term accepted
      change InputDerivation (view state holds) .empty rank term at accepted
      cases accepted
  | reference name =>
      intro rank environment complete term accepted
      have current := complete name (by simp [freeNames, Value.free, internedName]) rank (Nat.le_refl _) term accepted
      simpa only [shape, meaning] using current
  | node entry edges depth free originals ih =>
      intro rank environment complete term accepted
      change InputDerivation (view state holds) (.node entry.identity) rank term at accepted
      cases accepted with
      | node selectedRow present terms childrenAccepted guard =>
          rw [rows_readback state facts holds entry edges depth free available] at present
          obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
          apply (shape_node_meaning holds environment entry edges depth free _).mpr
          refine ⟨edge, inEdges, terms, rfl, ?_, guard⟩
          have forestAccepted := (input_forest_exact (view state holds) rank _ terms).mp childrenAccepted
          have mapped := (SymbolicGraphView.all₂_map_iff _ inputOf edge.children terms).mp forestAccepted
          apply SourcePhysicalSharedRows.all₂_both_imp _ _ edge.children terms mapped
          intro child inside term _ accepted
          obtain ⟨smaller, bounded, derivation⟩ := accepted
          apply ih edge inEdges child inside (available.children child (List.mem_flatMap.mpr ⟨edge, inEdges, inside⟩)) smaller environment ?_ term derivation
          intro name named before less term derivation
          exact complete name (node_free_child state facts entry edges depth free available edge inEdges child inside name named)
            before (Nat.le_trans less bounded) term derivation
  | union entry members depth free originals ih =>
      intro rank environment complete term accepted
      change InputDerivation (view state holds) (.union entry.identity) rank term at accepted
      cases accepted with
      | union member derivation bounded =>
          rw [members_readback state facts holds entry members depth free available] at member
          obtain ⟨child, inMembers, rfl⟩ := List.mem_map.mp member
          apply (shape_union_meaning holds environment entry members depth free term).mpr
          refine ⟨child, inMembers, ?_⟩
          apply ih child inMembers (available.children child inMembers) _ environment ?_ term derivation
          intro name named before less term derivation
          exact complete name (union_free_child state facts entry members depth free available child inMembers name named)
            before (Nat.le_trans less bounded) term derivation
  | mu entry body depth ordinary original ih =>
      intro rank environment complete term accepted
      change InputDerivation (view state holds) (.mu entry.identity) rank term at accepted
      simp only [shape, meaning]
      intro candidate candidateClosed
      have bodyAvailable := available.children body (by simp [children])
      have bodySource := body_readback state facts holds entry body depth ordinary available
      have contains : ∀ before, before ≤ rank → ∀ term,
          InputDerivation (view state holds) (.mu entry.identity) before term → candidate term := by
        intro before
        induction before using Nat.strongRecOn with
        | ind before inner =>
            intro bounded term derivation
            cases derivation with
            | binder bodyDerivation less =>
                apply candidateClosed term
                rw [bodySource] at bodyDerivation
                apply ih bodyAvailable _ (BinderLanguage.bind environment entry.identity candidate) ?_ term bodyDerivation
                intro name named smaller smallerBound term referenceDerivation
                by_cases same : name = entry.identity
                · subst name
                  simp only [BinderLanguage.bind, ite_true]
                  exact inner smaller (Nat.lt_of_le_of_lt smallerBound less)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt smallerBound less)) bounded) term
                    ((input_derivation_reference (view state holds) entry.identity smaller term).mp referenceDerivation)
                · simp only [BinderLanguage.bind, ite_eq_right same]
                  exact complete name ((mu_free_member entry body depth ordinary name).mpr ⟨named, same⟩)
                    smaller (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt smallerBound less)) bounded) term referenceDerivation
      exact contains rank (Nat.le_refl _) term accepted

end MicroCFTA.SourceRecursiveIntersectionInputView
