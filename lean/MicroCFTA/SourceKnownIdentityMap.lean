import MicroCFTA.SourceQuotientQueries

/-!
# Reverse identity transport for known source actuals

A source No is possible only when every active actual identity is known.
Restricting the actual quotient to those identities gives unique targets.
Its reverse preserves ambient values and every active actual value.
-/
namespace MicroCFTA.SourceKnownIdentityMap
open FullSyntax FormulaSubstitution SourceFormula SourceObservations SourceLogicalNames
open SourceIdentityQuotient SourceQuotientEnvironment
open SourceGuards (Guard Actual Resolved)

/-- Select exactly the actual records whose sparse identity flag is known. -/
def known (term : Language.Term (Label Formula)) (guard : Guard Formula) : List (Actual Formula) :=
  (SourceGuards.actuals (observe term) guard).filter (fun actual =>
    !(SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard).contains actual.target)

/-- Pair the two executed logical names only at known actuals. -/
def names (term : Language.Term (Label Formula)) (guard : Guard Formula) : List (Name × Name) :=
  ((known term guard).map fun actual =>
    (logicalName operations (observe term) (sameShape operations (observe term) []) guard actual,
     logicalName operations (observe term) (sameTerm operations term []) guard actual)).eraseDups

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

/-- A known actual contributes its exact source and target logical names. -/
theorem name_member (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ SourceGuards.actuals (observe term) guard)
    (isKnown : actual.target ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard) :
    (logicalName operations (observe term) (sameShape operations (observe term) []) guard actual,
      logicalName operations (observe term) (sameTerm operations term []) guard actual) ∈ names term guard := by
  simp only [names, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨actual, by simpa [known] using And.intro member isKnown, rfl⟩

/-- Restriction does not change the source functional-map property. -/
theorem functional (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Name × Name)
    (left : first ∈ names term guard) (right : second ∈ names term guard) (same : first.1 = second.1) : first = second := by
  apply SourceIdentityMap.functional operations term guard first second _ _ same
  all_goals
    simp only [names, List.mem_eraseDups] at left right
    simp only [SourceIdentityMap.names, List.mem_eraseDups]
  · obtain ⟨actual, member, equal⟩ := List.mem_map.mp left
    exact List.mem_map.mpr ⟨actual, (List.mem_filter.mp member).1, equal⟩
  · obtain ⟨actual, member, equal⟩ := List.mem_map.mp right
    exact List.mem_map.mpr ⟨actual, (List.mem_filter.mp member).1, equal⟩

/-- Equal complete names of known actuals already have equal sparse names. -/
theorem inverse_functional (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Name × Name)
    (left : first ∈ names term guard) (right : second ∈ names term guard) (same : first.2 = second.2) : first = second := by
  simp only [names, List.mem_eraseDups] at left right
  obtain ⟨a, am, ae⟩ := List.mem_map.mp left
  obtain ⟨b, bm, be⟩ := List.mem_map.mp right
  subst first; subst second
  have aMember := (List.mem_filter.mp am).1
  have bMember := (List.mem_filter.mp bm).1
  have aKnown : a.target ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard := by
    simpa using (List.mem_filter.mp am).2
  have representatives := logicalName_class operations (observe term) (sameTerm operations term []) guard a b aMember bMember same
  have trees : Language.Term.atPath term a.target = Language.Term.atPath term b.target := by
    rw [← ActualQuotient.complete_representative_same operations term guard a aMember,
      ← ActualQuotient.complete_representative_same operations term guard b bMember, representatives]
  have sparse := known_class term guard a b aMember bMember aKnown trees
  have labels := ActualQuotient.actual_labels_equal term guard a b aMember bMember trees
  exact Prod.ext (by simp only [logicalName, sparse, labels.1]) same

/-- The restricted actual map has unique source keys and unique complete targets. -/
theorem unique (term : Language.Term (Label Formula)) (guard : Guard Formula) :
    ((names term guard).map Prod.fst).Nodup ∧ ((names term guard).map Prod.snd).Nodup := by
  have pairs : (names term guard).Nodup := eraseDups_nodup _
  constructor
  · rw [List.Nodup, List.pairwise_map]
    apply pairs.imp_of_mem
    intro first second left right different equal
    exact different (functional term guard first second left right equal)
  · rw [List.Nodup, List.pairwise_map]
    apply pairs.imp_of_mem
    intro first second left right different equal
    exact different (inverse_functional term guard first second left right equal)

/-- A known actual cannot change its allocation status. -/
theorem original_iff (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ SourceGuards.actuals (observe term) guard)
    (isKnown : actual.target ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard) :
    logicalName operations (observe term) (sameShape operations (observe term) []) guard actual = actual.name ↔
      logicalName operations (observe term) (sameTerm operations term []) guard actual = actual.name := by
  constructor
  · intro original
    exact SourceIdentityMap.unallocated_fixed operations term guard actual member
      ((logical_original term guard _ actual member).mp original)
  · intro original
    exact (logical_original term guard _ actual member).mpr
      (known_unallocated term guard actual member isKnown ((logical_original term guard _ actual member).mp original))

/-- The reverse of the known-actual map fixes every original source name. -/
theorem reverse_fixed (term : Language.Term (Label Formula)) (guard : Guard Formula) (name : Name)
    (used : name ∈ SourceGuards.usedNames operations (observe term) guard) :
    renameName ((names term guard).map Prod.swap) name = name := by
  by_cases key : name ∈ ((names term guard).map Prod.swap).map Prod.fst
  · obtain ⟨swapped, present, field⟩ := List.mem_map.mp key
    obtain ⟨pair, member, swappedEq⟩ := List.mem_map.mp present
    subst swapped
    simp only [names, List.mem_eraseDups] at member
    obtain ⟨actual, actualMember, pairEq⟩ := List.mem_map.mp member
    subst pair
    have originalMember := (List.mem_filter.mp actualMember).1
    have isKnown : actual.target ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard := by
      simpa using (List.mem_filter.mp actualMember).2
    have targetName : logicalName operations (observe term) (sameTerm operations term []) guard actual = name := field
    have targetUsed : logicalName operations (observe term) (sameTerm operations term []) guard actual ∈
        SourceGuards.usedNames operations (observe term) guard := targetName.symm ▸ used
    have targetOriginal := (logical_shape term guard (sameTerm operations term []) actual).resolve_right
      (fun fresh => fresh targetUsed)
    have sourceOriginal := (original_iff term guard actual originalMember isKnown).mpr targetOriginal
    have selected := FreshEnvironment.rename_of_member ((names term guard).map Prod.swap)
      (by simpa [List.map_map, Function.comp_def] using (unique term guard).2) _ _
      (List.mem_map.mpr ⟨_, name_member term guard actual originalMember isKnown, rfl⟩)
    rw [targetName] at selected
    exact selected.trans (sourceOriginal.trans (targetOriginal.symm.trans targetName))
  · exact FormulaBinders.rename_absent _ _ key

/-- Build the complete environment that realizes every known sparse actual value. -/
noncomputable def lift (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) : Name → Value :=
  renamedEnvironment model env ((names term guard).map Prod.swap)

/-- The constructed reverse environment keeps all ambient values. -/
theorem ambient_values (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) :
    FormulaSemantics.Agree (SourceGuards.usedNames operations (observe term) guard) (lift model term guard env) env := by
  intro name member
  rw [lift, FreshEnvironment.environment_names model env _
    (by simpa [List.map_map, Function.comp_def] using (unique term guard).2), reverse_fixed term guard name member]

/-- The constructed reverse environment realizes the sparse value of each known actual. -/
theorem actual_value (model : Interpretation Value) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (env : Name → Value) (actual : Actual Formula)
    (member : actual ∈ SourceGuards.actuals (observe term) guard)
    (isKnown : actual.target ∉ SourceGuards.ambiguous (observe term) (sameShape operations (observe term) []) guard) :
    lift model term guard env (logicalName operations (observe term) (sameTerm operations term []) guard actual) =
      env (logicalName operations (observe term) (sameShape operations (observe term) []) guard actual) := by
  rw [lift, FreshEnvironment.environment_names model env _
    (by simpa [List.map_map, Function.comp_def] using (unique term guard).2)]
  rw [FreshEnvironment.rename_of_member ((names term guard).map Prod.swap)
    (by simpa [List.map_map, Function.comp_def] using (unique term guard).2) _ _
    (List.mem_map.mpr ⟨_, name_member term guard actual member isKnown, rfl⟩)]

/-- Local record correspondence reverses when the sparse identity is known. -/
theorem pair_reverse (paired : Pair ambient old new) (isKnown : old.identityKnown = true) : Pair ambient new old := by
  have completeOriginal : new.replacement.2 = old.symbolReplacement.2 → old.replacement.2 = old.symbolReplacement.2 := by
    intro original
    by_cases before : old.replacement.2 = old.symbolReplacement.2
    · exact before
    · have impossible := paired.becomesOriginal before original
      simp [isKnown] at impossible
  constructor
  · exact paired.symbols.symm
  · rw [paired.symbols]; exact paired.newFormal
  · rw [paired.symbols]; exact paired.oldFormal
  · rw [paired.symbols]; exact paired.formalLive
  · rw [paired.symbols]; exact paired.actualLive
  · rw [paired.symbols]; exact paired.newShape
  · rw [paired.symbols]; exact paired.oldShape
  · rw [paired.symbols]; exact completeOriginal
  · rw [paired.symbols]
    intro before original
    exact False.elim (before (paired.retained original))

end MicroCFTA.SourceKnownIdentityMap
