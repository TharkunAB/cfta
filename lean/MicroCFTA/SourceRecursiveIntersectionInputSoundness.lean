import MicroCFTA.SourceRecursiveIntersectionInputLanguage

/-!
# Sound copied language of original physical inputs

Every term accepted by copied original syntax has an independent finite
input derivation. Open free environments retain their explicit soundness
premise. Recursive binder soundness uses its least-language property.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule Language

/-- Copied original physical syntax produces only independent finite input derivations. -/
theorem Original.copy_sound (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) : ∀ environment, SoundEnvironment state holds value environment →
      Included (meaning environment (shape holds value)) (InputLanguage state holds (inputOf value)) := by
  induction original with
  | empty => intro environment sound term accepted; simp [shape, meaning] at accepted
  | reference name =>
      intro environment sound term accepted
      exact sound name (by simp [freeNames, Value.free, internedName]) term (by simpa [shape, meaning] using accepted)
  | node entry edges depth free originals ih =>
      intro environment sound term accepted
      obtain ⟨edge, present, terms, same, childrenAccepted, guard⟩ :=
        (shape_node_meaning holds environment entry edges depth free term).mp accepted
      apply (input_node_exact (view state holds) entry.identity term).mpr
      refine ⟨row holds edge, ?_, terms, same, ?_, guard⟩
      · rw [rows_readback state facts holds entry edges depth free available]
        exact List.mem_map.mpr ⟨edge, present, rfl⟩
      · apply (SymbolicGraphView.all₂_map_iff _ inputOf edge.children terms).mpr
        apply SourcePhysicalSharedRows.all₂_both_imp _ _ edge.children terms childrenAccepted
        intro child inside term _ accepted
        apply ih edge present child inside (available.children child (List.mem_flatMap.mpr ⟨edge, present, inside⟩)) environment
          (fun name named => sound name (node_free_child state facts entry edges depth free available edge present child inside name named)) term accepted
  | union entry members depth free originals ih =>
      intro environment sound term accepted
      obtain ⟨child, member, accepted⟩ := (shape_union_meaning holds environment entry members depth free term).mp accepted
      apply (input_union_exact (view state holds) entry.identity term).mpr
      refine ⟨inputOf child, ?_, ?_⟩
      · rw [members_readback state facts holds entry members depth free available]
        exact List.mem_map.mpr ⟨child, member, rfl⟩
      · exact ih child member (available.children child member) environment
          (fun name named => sound name (union_free_child state facts entry members depth free available child member name named)) term accepted
  | mu entry body depth ordinary original ih =>
      intro environment sound term accepted
      let target := InputLanguage state holds (.mu entry.identity)
      have bodyAvailable := available.children body (by simp [children])
      have bodySource := body_readback state facts holds entry body depth ordinary available
      have contained : Included (meaning (BinderLanguage.bind environment entry.identity target) (shape holds body)) target := by
        intro term accepted
        apply (input_binder_exact (view state holds) entry.identity term).mpr
        rw [bodySource]
        apply ih bodyAvailable (BinderLanguage.bind environment entry.identity target) ?_ term accepted
        intro name member term before
        by_cases same : name = entry.identity
        · subst name
          have current : target term := by simpa only [BinderLanguage.bind, ite_true] using before
          obtain ⟨rank, accepted⟩ := current
          exact ⟨rank, (input_derivation_reference (view state holds) entry.identity rank term).mpr accepted⟩
        · apply sound name ((mu_free_member entry body depth ordinary name).mpr ⟨member, same⟩) term
          simpa only [BinderLanguage.bind, ite_eq_right same] using before
      exact least_le _ target contained term (by simpa only [shape, meaning] using accepted)

end MicroCFTA.SourceRecursiveIntersectionInputView
