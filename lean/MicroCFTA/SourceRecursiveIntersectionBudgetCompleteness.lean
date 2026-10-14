import MicroCFTA.SourceRecursiveIntersectionBudgetInput

/-!
# Complete stored meanings at each input unfolding budget

Every finite actual input derivation is accepted at its original bound.
Upward free environments retain smaller child derivations. Strong induction
on the unfolding bound handles recursive binder occurrences.
-/
namespace MicroCFTA.SourceRecursiveIntersectionBudgetInput
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectSchedule SourceRecursiveIntersectionInputView

/-- Original records contain every actual input derivation at its original bound. -/
theorem original_complete (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) : ∀ budget environment,
      (∀ name, BinderBudgetLanguage.Upward (environment name)) →
      CompleteEnvironment state holds value budget environment → ∀ term,
      InputDerivation (view state holds) (inputOf value) budget term →
        InternedGuardedBudget.meaning holds environment value budget term := by
  induction original with
  | empty =>
      intro budget environment upward complete term accepted
      change InputDerivation (view state holds) .empty budget term at accepted
      cases accepted
  | reference name =>
      intro budget environment upward complete term accepted
      rw [InternedGuardedBudget.meaning]
      exact complete name (by simp [freeNames, Value.free, internedName]) budget (Nat.le_refl _) term accepted
  | node entry edges depth free originals ih =>
      intro budget environment upward complete term accepted
      change InputDerivation (view state holds) (.node entry.identity) budget term at accepted
      cases accepted with
      | node selectedRow present terms childrenAccepted guard =>
          rw [rows_readback state facts holds entry edges depth free available] at present
          obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
          rw [InternedGuardedBudget.meaning]
          refine ⟨⟨edge, inEdges⟩, ?_⟩
          cases edge with
          | mk edgeEntry children =>
              rw [InternedGuardedBudget.edgeMeaning]
              refine ⟨terms, rfl, ?_, guard⟩
              apply (InternedGuardedBudget.forest_all holds environment budget children terms).mpr
              have forestAccepted := (input_forest_exact (view state holds) budget _ terms).mp childrenAccepted
              have mapped := (SymbolicGraphView.all₂_map_iff _ inputOf children terms).mp forestAccepted
              apply SourcePhysicalSharedRows.all₂_both_imp _ _ children terms mapped
              intro child inside term _ accepted
              obtain ⟨smaller, bounded, derivation⟩ := accepted
              apply InternedGuardedBudget.meaning_upward holds child environment upward smaller budget bounded term
              apply ih _ inEdges child inside
                (available.children child (List.mem_flatMap.mpr ⟨_, inEdges, inside⟩)) smaller environment upward ?_ term derivation
              intro name named before less term derivation
              exact complete name
                (node_free_child state facts entry edges depth free available _ inEdges child inside name named)
                before (Nat.le_trans less bounded) term derivation
  | union entry members depth free originals ih =>
      intro budget environment upward complete term accepted
      change InputDerivation (view state holds) (.union entry.identity) budget term at accepted
      cases accepted with
      | union member derivation bounded =>
          rw [members_readback state facts holds entry members depth free available] at member
          obtain ⟨child, inMembers, rfl⟩ := List.mem_map.mp member
          rw [InternedGuardedBudget.meaning]
          refine ⟨⟨child, inMembers⟩, ?_⟩
          apply InternedGuardedBudget.meaning_upward holds child environment upward _ budget bounded term
          apply ih child inMembers (available.children child inMembers) _ environment upward ?_ term derivation
          intro name named before less term derivation
          exact complete name (union_free_child state facts entry members depth free available child inMembers name named)
            before (Nat.le_trans less bounded) term derivation
  | mu entry body depth ordinary original ih =>
      intro budget environment upward complete term accepted
      change InputDerivation (view state holds) (.mu entry.identity) budget term at accepted
      rw [InternedGuardedBudget.meaning]
      intro candidate candidateUpward candidateClosed
      have bodyAvailable := available.children body (by simp [children])
      have bodySource := body_readback state facts holds entry body depth ordinary available
      have boundUpward : ∀ name, BinderBudgetLanguage.Upward
          (InternedGuardedBudget.bind environment (.interned entry.identity) candidate name) := by
        intro name
        by_cases same : name = .interned entry.identity
        · simpa only [InternedGuardedBudget.bind, same, ite_true] using candidateUpward
        · simpa only [InternedGuardedBudget.bind, ite_eq_right same] using upward name
      have contains : ∀ before, before ≤ budget → ∀ term,
          InputDerivation (view state holds) (.mu entry.identity) before term → candidate before term := by
        intro before
        induction before using Nat.strongRecOn with
        | ind before inner =>
            intro bounded term derivation
            cases derivation with
            | binder bodyDerivation less =>
                apply candidateClosed before term
                refine ⟨_, less, ?_⟩
                rw [bodySource] at bodyDerivation
                apply ih bodyAvailable _ (InternedGuardedBudget.bind environment (.interned entry.identity) candidate)
                  boundUpward ?_ term bodyDerivation
                intro name named smaller smallerBound term referenceDerivation
                by_cases same : name = entry.identity
                · subst name
                  simp only [InternedGuardedBudget.bind, ite_true]
                  exact inner smaller (Nat.lt_of_le_of_lt smallerBound less)
                    (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt smallerBound less)) bounded) term
                    ((input_derivation_reference (view state holds) entry.identity smaller term).mp referenceDerivation)
                · simp only [InternedGuardedBudget.bind, Reference.interned.injEq, ite_eq_right same]
                  exact complete name ((mu_free_member entry body depth ordinary name).mpr ⟨named, same⟩)
                    smaller (Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt smallerBound less)) bounded) term referenceDerivation
      exact contains budget (Nat.le_refl _) term accepted

end MicroCFTA.SourceRecursiveIntersectionBudgetInput
