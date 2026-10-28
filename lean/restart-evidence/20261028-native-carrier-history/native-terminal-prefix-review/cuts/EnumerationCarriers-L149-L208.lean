            have intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged := by
              cases sourceNode <;> cases targetNode <;> rfl
            simp only [intersection] at continued
            obtain ⟨ignored, checked, required, _⟩ := (success_bind _ _ _ _ _).mp continued
            cases ignored
            have notEmpty : hasEmptyContents graph merged = false := by simpa using ((require_success _ before checked).mp required).1
            have execution := assimilate_exact graph before target source sourceNode targetNode sourceScs targetScs merged same sourceRead targetRead intersection notEmpty
            have afterSame : after = assimilated before target source merged := by simpa [Success, execution, ExceptT.run] using original
            rw [afterSame]
            exact assimilated_carriers graph before target source _ _ merged same sourceRead targetRead intersection related

/-- The complete terminal merge preserves each graph-bearing class through duplicate assimilation. -/
theorem mergeTerminal_carriers (graph : Graph Symbol Guard) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (before after : State Symbol Guard) (target : Nat) (total : UnionFind.Total before.representatives)
    (success : Success (mergeTerminal graph fuel first rest) before target after) : PreservesCarriers before after := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold mergeTerminal at success
  obtain ⟨recorded, scanned, scan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest) before scanned recorded ⟨rfl, paths⟩ scan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united := terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
    (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨winner, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var winner united resolved joined resolution
  obtain ⟨ignored, assimilated, assimilation, final⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  obtain ⟨_, afterSame⟩ := (success_pure winner target assimilated after).mp final
  subst after
  have resolvedCarriers : PreservesCarriers before resolved := carriers_classes before resolved resolvedValid.values
    (fun left right same => (resolvedValid.joined left right).mpr (Or.inl ((class_iff before.representatives roots paths left right).mp same)))
  have selectedMember : ∀ sc ∈ first :: rest, roots sc.var ∈ selected := by
    intro sc member
    apply (resolve_members roots rest [roots first.var] (roots sc.var)).mpr
    rcases List.mem_cons.mp member with rfl | present
    · exact Or.inl (by simp)
    · exact Or.inr ⟨sc, present, rfl⟩
  have relatedRecorded : ∀ source ∈ recorded, UnionFind.SameClass resolved.representatives winner source := by
    intro source member
    rw [recordedSame] at member
    obtain ⟨sc, present, rfl⟩ := List.mem_map.mp member
    have fixed : roots (roots sc.var) = roots sc.var := by
      obtain ⟨size, original⟩ := paths sc.var
      exact (root_iff before.representatives roots paths (roots sc.var)).mp ⟨size, .root (UnionFind.reaches_terminal original)⟩
    exact UnionFind.sameClass_trans (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
      ((resolvedValid.joined first.var (roots sc.var)).mpr (Or.inr ⟨selectedMember first (by simp), by simpa [fixed] using selectedMember sc present⟩))
  have traversed := forM_invariant (EnumerationState.assimilate graph winner)
    (fun state : State Symbol Guard => state.representatives = resolved.representatives ∧ PreservesCarriers resolved state) recorded
    (by
      intro source member previous next valid execution
      have preserves := assimilate_carriers graph winner source previous next (by simpa [valid.1] using relatedRecorded source member) execution
      exact ⟨(assimilate_effect graph previous next winner source execution).1.trans valid.1, valid.2.trans preserves⟩)
    resolved assimilated ⟨rfl, .refl resolved⟩ assimilation
  exact resolvedCarriers.trans traversed.2

/-- A reached graph restriction preserves all old carriers and supplies one for its returned variable. -/
theorem mergeNode_carriers (graph : Graph Symbol Guard) (fuel uv node : Nat) (scs : List Suspended)
    (before after : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (success : Success (mergeNode graph fuel uv node scs) before () after) :
