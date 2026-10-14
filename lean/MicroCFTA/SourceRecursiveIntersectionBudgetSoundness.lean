import MicroCFTA.SourceRecursiveIntersectionBudgetInput

/-!
# Sound stored meanings at each input unfolding budget

Every accepted original record has an actual input derivation at the same
budget. A raw Mu consumes one step. Guards and ordered children stay exact.
-/
namespace MicroCFTA.SourceRecursiveIntersectionBudgetInput
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectSchedule SourceRecursiveIntersectionInputView

/-- Budgeted original records produce actual finite input derivations at the same bound. -/
theorem original_sound (state : State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) : ∀ environment, SoundEnvironment state holds value environment →
      ∀ budget term, InternedGuardedBudget.meaning holds environment value budget term →
        InputDerivation (view state holds) (inputOf value) budget term := by
  induction original with
  | empty =>
      intro environment sound budget term accepted
      rw [InternedGuardedBudget.meaning] at accepted
      exact accepted.elim
  | reference name =>
      intro environment sound budget term accepted
      exact sound name (by simp [freeNames, Value.free, internedName]) budget term
        (by simpa only [InternedGuardedBudget.meaning] using accepted)
  | node entry edges depth free originals ih =>
      intro environment sound budget term accepted
      rw [InternedGuardedBudget.meaning] at accepted
      obtain ⟨⟨edge, present⟩, accepted⟩ := accepted
      cases edge with
      | mk edgeEntry children =>
          rw [InternedGuardedBudget.edgeMeaning] at accepted
          obtain ⟨terms, same, childrenAccepted, guard⟩ := accepted
          subst term
          apply InputDerivation.node (row holds (.mk edgeEntry children)) ?_ terms ?_ guard
          · rw [rows_readback state facts holds entry edges depth free available]
            exact List.mem_map.mpr ⟨_, present, rfl⟩
          · apply (input_forest_exact (view state holds) budget _ terms).mpr
            apply (SymbolicGraphView.all₂_map_iff _ inputOf children terms).mpr
            apply SourcePhysicalSharedRows.all₂_both_imp _ _ children terms
              ((InternedGuardedBudget.forest_all holds environment budget children terms).mp childrenAccepted)
            intro child inside term _ accepted
            refine ⟨budget, Nat.le_refl _, ?_⟩
            exact ih _ present child inside
              (available.children child (List.mem_flatMap.mpr ⟨_, present, inside⟩)) environment
              (fun name named => sound name
                (node_free_child state facts entry edges depth free available _ present child inside name named))
              budget term accepted
  | union entry members depth free originals ih =>
      intro environment sound budget term accepted
      rw [InternedGuardedBudget.meaning] at accepted
      obtain ⟨⟨child, member⟩, accepted⟩ := accepted
      apply InputDerivation.union (child := inputOf child) ?_ ?_ (Nat.le_refl budget)
      · rw [members_readback state facts holds entry members depth free available]
        exact List.mem_map.mpr ⟨child, member, rfl⟩
      · exact ih child member (available.children child member) environment
          (fun name named => sound name
            (union_free_child state facts entry members depth free available child member name named))
          budget term accepted
  | mu entry body depth ordinary original ih =>
      intro environment sound budget term accepted
      let target : BinderBudgetLanguage.Lang Symbol :=
        fun bound term => InputDerivation (view state holds) (.mu entry.identity) bound term
      have upward : BinderBudgetLanguage.Upward target :=
        fun before after bounded term derivation => input_derivation_mono _ _ before after bounded term derivation
      have bodyAvailable := available.children body (by simp [children])
      have bodySource := body_readback state facts holds entry body depth ordinary available
      rw [InternedGuardedBudget.meaning] at accepted
      apply accepted target upward
      rintro bound term ⟨smaller, less, bodyAccepted⟩
      apply InputDerivation.binder (smaller := smaller) ?_ less
      rw [bodySource]
      apply ih bodyAvailable (InternedGuardedBudget.bind environment (.interned entry.identity) target) ?_
        smaller term bodyAccepted
      intro name member bound term before
      by_cases same : name = entry.identity
      · subst name
        apply (input_derivation_reference (view state holds) entry.identity bound term).mpr
        simpa only [InternedGuardedBudget.bind, ite_true] using before
      · apply sound name ((mu_free_member entry body depth ordinary name).mpr ⟨member, same⟩) bound term
        simpa only [InternedGuardedBudget.bind, Reference.interned.injEq, ite_eq_right same] using before

end MicroCFTA.SourceRecursiveIntersectionBudgetInput
