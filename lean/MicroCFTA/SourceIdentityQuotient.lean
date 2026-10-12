import MicroCFTA.SourceQuotientEnvironment

/-!
# Actual source records under the complete identity quotient

These lemmas derive the local forward-environment invariants from the source
allocator. They permit complete declarations to disappear and unknown
identity flags to become known.
-/
namespace MicroCFTA.SourceIdentityQuotient
open FullSyntax SourceFormula SourceGuards SourceObservations SourceLogicalNames
open FormulaSubstitution SourceQuotientEnvironment

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (items : List α) : items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp only [List.mem_eraseDups, List.mem_filter]
        intro member
        simpa using member.2
      · exact eraseDups_nodup _
termination_by items.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- A known actual already shares its sparse representative with every equal complete actual. -/
theorem known_class (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (actual other : Actual Formula) (member : actual ∈ actuals (observe term) guard)
    (otherMember : other ∈ actuals (observe term) guard)
    (known : actual.target ∉ ambiguous (observe term) (sameShape operations (observe term) []) guard)
    (same : Language.Term.atPath term actual.target = Language.Term.atPath term other.target) :
    representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) actual =
      representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) other := by
  by_cases leaf : (observe term actual.target).map Observed.leafness = some .leaf
  · exact ActualQuotient.sparse_leaf_canonical operations term guard actual other member otherMember same leaf
  · by_cases positions : actual.target = other.target
    · rw [actual_target_unique (observe term) guard actual other member otherMember positions]
    · exact False.elim (known (ActualQuotient.equal_inner_ambiguous operations term guard actual other member otherMember same positions leaf))

/-- Without a complete declaration, a known actual has at most one sparse representative for its name. -/
theorem known_count (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard)
    (known : actual.target ∉ ambiguous (observe term) (sameShape operations (observe term) []) guard)
    (absent : (allocated operations (observe term) (sameTerm operations term []) guard).lookup
      (representative (observe term) (sameTerm operations term []) (actuals (observe term) guard) actual) = none) :
    (values (observe term) (sameShape operations (observe term) []) guard).countP
      (fun value => decide (value.2 = actual.name)) ≤ 1 := by
  let key := (representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) actual, actual.name)
  have unique : (values (observe term) (sameShape operations (observe term) []) guard).Nodup := eraseDups_nodup _
  have bound := List.Nodup.length_le_of_subset (unique.filter (fun value => decide (value.2 = actual.name)))
    (l₂ := [key]) (by
      intro row present
      obtain ⟨valueMember, nameEq⟩ := List.mem_filter.mp present
      simp only [values, List.mem_eraseDups] at valueMember
      obtain ⟨other, otherMember, rowEq⟩ := List.mem_map.mp valueMember
      subst row
      have equalName : other.name = actual.name := by simpa using nameEq
      have complete := unallocated_same_class operations (observe term) (sameTerm operations term []) guard
        actual other member otherMember absent equalName.symm
      have trees : Language.Term.atPath term actual.target = Language.Term.atPath term other.target := by
        rw [← ActualQuotient.complete_representative_same operations term guard actual member,
          ← ActualQuotient.complete_representative_same operations term guard other otherMember, complete]
      have sparse := known_class term guard actual other member otherMember known trees
      simp only [List.mem_singleton]
      exact Prod.ext sparse.symm equalName)
  simpa only [List.countP_eq_length_filter, List.length_singleton] using bound

/-- A known sparse declaration cannot disappear when complete identity information is supplied. -/
theorem known_unallocated (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard)
    (known : actual.target ∉ ambiguous (observe term) (sameShape operations (observe term) []) guard)
    (absent : (allocated operations (observe term) (sameTerm operations term []) guard).lookup
      (representative (observe term) (sameTerm operations term []) (actuals (observe term) guard) actual) = none) :
    (allocated operations (observe term) (sameShape operations (observe term) []) guard).lookup
      (representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) actual) = none := by
  cases found : (allocated operations (observe term) (sameShape operations (observe term) []) guard).lookup
      (representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) actual) with
  | none => rfl
  | some binding =>
      have row := lookup_member _ _ _ found
      have conflict : (representative (observe term) (sameShape operations (observe term) []) (actuals (observe term) guard) actual, binding.2) ∈
          conflicts (observe term) (sameShape operations (observe term) []) guard := by
        rw [← allocated_sources operations (observe term) (sameShape operations (observe term) []) guard]
        exact List.mem_map.mpr ⟨_, row, rfl⟩
      have parts := List.mem_filter.mp conflict
      have valueMember := parts.1
      simp only [values, List.mem_eraseDups] at valueMember
      obtain ⟨other, otherMember, pairEq⟩ := List.mem_map.mp valueMember
      have names := (ActualQuotient.actual_labels_equal term guard other actual otherMember member
        (ActualQuotient.sparse_classes_refine_terms operations term guard other actual otherMember member
          (congrArg Prod.fst pairEq))).1
      have original : binding.2 = actual.name := (congrArg Prod.snd pairEq).symm.trans names
      have count : 1 < (values (observe term) (sameShape operations (observe term) []) guard).countP
          (fun value => decide (value.2 = actual.name)) := by simpa [original] using parts.2
      have bound := known_count term guard actual member known absent
      omega

/-- Every logical actual name is its original spelling or lies outside the source avoid set. -/
theorem logical_shape (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (actual : Actual Formula) :
    logicalName operations (observe term) sameAt guard actual = actual.name ∨
      logicalName operations (observe term) sameAt guard actual ∉ usedNames operations (observe term) guard := by
  cases found : (allocated operations (observe term) sameAt guard).lookup
      (representative (observe term) sameAt (actuals (observe term) guard) actual) with
  | none => exact Or.inl (by simp [logicalName, found])
  | some binding =>
      apply Or.inr
      simpa [logicalName, found] using SourceActuals.allocated_avoids operations (observe term) sameAt guard _ binding.1 binding.2
        (lookup_member _ _ _ found)

/-- An original logical name is exactly an absent allocated declaration. -/
theorem logical_original (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard) :
    logicalName operations (observe term) sameAt guard actual = actual.name ↔
      (allocated operations (observe term) sameAt guard).lookup
        (representative (observe term) sameAt (actuals (observe term) guard) actual) = none := by
  cases found : (allocated operations (observe term) sameAt guard).lookup
      (representative (observe term) sameAt (actuals (observe term) guard) actual) with
  | none => simp [logicalName, found]
  | some binding =>
      have fresh := SourceActuals.allocated_avoids operations (observe term) sameAt guard _ binding.1 binding.2
        (lookup_member _ _ _ found)
      have used := actual_name_used operations (observe term) guard actual member
      have different : binding.1 ≠ actual.name := fun equal => fresh (equal ▸ used)
      simp [logicalName, found, different]

/-- An actual whose fresh declaration disappears is explicitly marked identity-unknown in the sparse table. -/
theorem becomes_original_unknown (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard)
    (fresh : logicalName operations (observe term) (sameShape operations (observe term) []) guard actual ≠ actual.name)
    (original : logicalName operations (observe term) (sameTerm operations term []) guard actual = actual.name) :
    actual.target ∈ ambiguous (observe term) (sameShape operations (observe term) []) guard := by
  by_cases known : actual.target ∈ ambiguous (observe term) (sameShape operations (observe term) []) guard
  · exact known
  · exact False.elim (fresh ((logical_original term guard _ actual member).mpr
      (known_unallocated term guard actual member known ((logical_original term guard _ actual member).mp original))))

/-- Every present requested actual appears in the executed source actual table. -/
theorem actual_member (observed : Observations Formula) (guard : Guard Formula)
    (target : Path) (value : Observed Formula) (requested : target ∈ actualPaths guard)
    (found : observed target = some value) :
    (⟨target, value.name, value.refinement⟩ : Actual Formula) ∈ actuals observed guard := by
  apply List.mem_filterMap.mpr
  exact ⟨target, by simpa [orderedPaths] using requested, by simp [found]⟩

/-- Resolution exposes the logical identity selected by the exact allocator. -/
theorem resolved_row (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (entry : Substitution) (actual formal : Observed Formula)
    (requested : entry.actual ∈ actualPaths guard)
    (atActual : observe term entry.actual = some actual) (atFormal : observe term entry.formal = some formal)
    (resolved : Resolved Formula)
    (success : resolve operations (observe term) (substitutionValues operations (observe term) sameAt guard).1
      (substitutionValues operations (observe term) sameAt guard).2 entry = some resolved) :
    resolved =
      ⟨(formal.name, logicalName operations (observe term) sameAt guard ⟨entry.actual, actual.name, actual.refinement⟩),
       (formal.name, actual.name),
       substitute [(valueName, logicalName operations (observe term) sameAt guard ⟨entry.actual, actual.name, actual.refinement⟩)] actual.refinement,
       (substitutionValues operations (observe term) sameAt guard).1.lookup entry.actual,
       !(ambiguous (observe term) sameAt guard).contains entry.actual⟩ := by
  have copied := logicalName_copied operations (observe term) sameAt guard
    ⟨entry.actual, actual.name, actual.refinement⟩ (actual_member (observe term) guard entry.actual actual requested atActual)
  simp [resolve, atActual, atFormal] at success
  rw [← success]
  simp only [copied]
  simp [operations, substitutionValues]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Source resolution derives every local invariant needed by forward environment transport. -/
theorem resolve_pair (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (entry : Substitution) (actualRequested : entry.actual ∈ actualPaths guard)
    (formalRequested : entry.formal ∈ paths guard) (old new : Resolved Formula)
    (oldFound : resolve operations (observe term)
      (substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : resolve operations (observe term)
      (substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new) :
    Pair (usedNames operations (observe term) guard) old new := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  rw [resolved_row term guard _ entry actual formal actualRequested atActual atFormal old oldFound,
    resolved_row term guard _ entry actual formal actualRequested atActual atFormal new newFound]
  let record : Actual Formula := ⟨entry.actual, actual.name, actual.refinement⟩
  have member : record ∈ actuals (observe term) guard := actual_member (observe term) guard entry.actual actual actualRequested atActual
  constructor
  · rfl
  · rfl
  · rfl
  · exact SourceResolvedTables.used_at operations (observe term) guard entry.formal formal formalRequested atFormal
  · exact actual_name_used operations (observe term) guard record member
  · exact logical_shape term guard _ record
  · exact logical_shape term guard _ record
  · intro original
    exact SourceIdentityMap.unallocated_fixed operations term guard record member
      ((logical_original term guard _ record member).mp original)
  · intro fresh original
    have unknown := becomes_original_unknown term guard record member fresh original
    simpa [record] using unknown

/-- The constructed source identity map supplies corresponding values for every resolved actual. -/
theorem resolve_values (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (entry : Substitution) (requested : entry.actual ∈ actualPaths guard) (old new : Resolved Formula)
    (oldFound : resolve operations (observe term)
      (substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).1
      (substitutionValues operations (observe term) (sameShape operations (observe term) []) guard).2 entry = some old)
    (newFound : resolve operations (observe term)
      (substitutionValues operations (observe term) (sameTerm operations term []) guard).1
      (substitutionValues operations (observe term) (sameTerm operations term []) guard).2 entry = some new)
    (env : FullSyntax.Name → Value) :
    renamedEnvironment model env (SourceIdentityMap.names operations term guard) old.replacement.2 = env new.replacement.2 := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists operations (observe term) _ _ entry old oldFound
  rw [resolved_row term guard _ entry actual formal requested atActual atFormal old oldFound,
    resolved_row term guard _ entry actual formal requested atActual atFormal new newFound]
  exact SourceIdentityMap.environment_actual model operations term guard env
    ⟨entry.actual, actual.name, actual.refinement⟩ (actual_member (observe term) guard entry.actual actual requested atActual)

/-- Pullback along the actual quotient preserves every original source name. -/
theorem ambient_values (model : Interpretation Value) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (env : FullSyntax.Name → Value) : FormulaSemantics.Agree (usedNames operations (observe term) guard)
      (renamedEnvironment model env (SourceIdentityMap.names operations term guard)) env := by
  intro name member
  rw [FreshEnvironment.environment_names model env _ (SourceIdentityMap.keys_unique operations term guard),
    SourceIdentityMap.used_fixed operations term guard name member]

/-- A chosen representative is a stored actual with the same original name. -/
theorem representative_named (observed : Observations Formula) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (actual : Actual Formula) (member : actual ∈ actuals observed guard) :
    ∃ chosen ∈ actuals observed guard,
      representative observed sameAt (actuals observed guard) actual = chosen.target ∧ chosen.name = actual.name := by
  unfold representative
  split
  · rename_i chosen selected
    refine ⟨chosen, List.mem_of_find?_eq_some selected, rfl, ?_⟩
    have properties := List.find?_some selected
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at properties
    exact properties.1.1
  · exact ⟨actual, member, rfl, rfl⟩

/-- Source representative equality cannot identify different original sort names. -/
theorem representative_names (observed : Observations Formula) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (first second : Actual Formula)
    (left : first ∈ actuals observed guard) (right : second ∈ actuals observed guard)
    (same : representative observed sameAt (actuals observed guard) first =
      representative observed sameAt (actuals observed guard) second) : first.name = second.name := by
  obtain ⟨a, am, apos, an⟩ := representative_named observed guard sameAt first left
  obtain ⟨b, bm, bt, bn⟩ := representative_named observed guard sameAt second right
  have equal := actual_target_unique observed guard a b am bm (apos.symm.trans (same.trans bt))
  exact an.symm.trans ((congrArg Actual.name equal).trans bn)

/-- Every allocated declaration retains the original name of the actual it represents. -/
theorem allocation_original (observed : Observations Formula) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (actual : Actual Formula) (member : actual ∈ actuals observed guard)
    (binding : FullSyntax.Name × FullSyntax.Name)
    (found : (allocated operations observed sameAt guard).lookup
      (representative observed sameAt (actuals observed guard) actual) = some binding) : binding.2 = actual.name := by
  have row := lookup_member _ _ _ found
  have conflict : (representative observed sameAt (actuals observed guard) actual, binding.2) ∈
      conflicts observed sameAt guard := by
    rw [← allocated_sources operations observed sameAt guard]
    exact List.mem_map.mpr ⟨_, row, rfl⟩
  have valueMember := (List.mem_filter.mp conflict).1
  simp only [values, List.mem_eraseDups] at valueMember
  obtain ⟨other, otherMember, pairEq⟩ := List.mem_map.mp valueMember
  exact (congrArg Prod.snd pairEq).symm.trans
    (representative_names observed guard sameAt other actual otherMember member (congrArg Prod.fst pairEq))

/-- A resolved fresh declaration names its logical actual and retains the original sort name. -/
theorem resolved_declaration (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (entry : Substitution) (actual formal : Observed Formula)
    (requested : entry.actual ∈ actualPaths guard)
    (atActual : observe term entry.actual = some actual) (atFormal : observe term entry.formal = some formal)
    (resolved : Resolved Formula)
    (success : resolve operations (observe term) (substitutionValues operations (observe term) sameAt guard).1
      (substitutionValues operations (observe term) sameAt guard).2 entry = some resolved)
    (binding : FullSyntax.Name × FullSyntax.Name) (declared : resolved.declaration = some binding) :
    binding.1 = resolved.replacement.2 ∧ binding.2 = actual.name := by
  have row := resolved_row term guard sameAt entry actual formal requested atActual atFormal resolved success
  rw [row] at declared ⊢
  have member := actual_member (observe term) guard entry.actual actual requested atActual
  have allocated : (SourceGuards.allocated operations (observe term) sameAt guard).lookup
      (representative (observe term) sameAt (actuals (observe term) guard) ⟨entry.actual, actual.name, actual.refinement⟩) = some binding := by
    rw [← copied_lookup operations (observe term) sameAt guard _ member]
    exact declared
  constructor
  · simp [logicalName, allocated]
  · exact allocation_original (observe term) guard sameAt _ member binding allocated

/-- When resolution has no declaration, its logical actual has the ambient original name. -/
theorem resolved_undeclared (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (sameAt : Path → Path → Option Bool) (entry : Substitution) (actual formal : Observed Formula)
    (requested : entry.actual ∈ actualPaths guard)
    (atActual : observe term entry.actual = some actual) (atFormal : observe term entry.formal = some formal)
    (resolved : Resolved Formula)
    (success : resolve operations (observe term) (substitutionValues operations (observe term) sameAt guard).1
      (substitutionValues operations (observe term) sameAt guard).2 entry = some resolved)
    (absent : resolved.declaration = none) : resolved.replacement.2 = actual.name := by
  have row := resolved_row term guard sameAt entry actual formal requested atActual atFormal resolved success
  rw [row] at absent ⊢
  have member := actual_member (observe term) guard entry.actual actual requested atActual
  apply (logical_original term guard sameAt _ member).mpr
  rw [← copied_lookup operations (observe term) sameAt guard _ member]
  exact absent

end MicroCFTA.SourceIdentityQuotient
