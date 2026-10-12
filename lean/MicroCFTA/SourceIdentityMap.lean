import MicroCFTA.SourceLogicalNames

/-!
# Construct the sparse-to-complete source identity map

The map pairs the source logical names at the same actual positions. It can
identify several sparse names. Duplicate source keys have the same target.
-/
namespace MicroCFTA.SourceIdentityMap
open SourceGuards SourceObservations SourceLogicalNames
open FormulaSubstitution

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

/-- Pair the executed source logical names at every existing actual position. -/
def names [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) : List (Name × Name) :=
  ((actuals (observe term) guard).map fun actual =>
    (logicalName formulas (observe term) (sameShape formulas (observe term) []) guard actual,
     logicalName formulas (observe term) (sameTerm formulas term []) guard actual)).eraseDups

/-- Every actual position contributes its exact sparse and complete name pair. -/
theorem name_member [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard) :
    (logicalName formulas (observe term) (sameShape formulas (observe term) []) guard actual,
     logicalName formulas (observe term) (sameTerm formulas term []) guard actual) ∈ names formulas term guard := by
  simp only [names, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨actual, member, rfl⟩

/-- The complete source name is uniquely determined by its sparse source name. -/
theorem functional [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (first second : Name × Name)
    (left : first ∈ names formulas term guard) (right : second ∈ names formulas term guard)
    (same : first.1 = second.1) : first = second := by
  simp only [names, List.mem_eraseDups] at left right
  obtain ⟨a, ha, ra⟩ := List.mem_map.mp left
  obtain ⟨b, hb, rb⟩ := List.mem_map.mp right
  subst first; subst second
  exact Prod.ext same (sparse_name_complete_name formulas term guard a b ha hb same)

/-- Removing duplicate pairs also removes duplicate source keys because the table is functional. -/
theorem keys_unique [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) : ((names formulas term guard).map Prod.fst).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  have pairs : (names formulas term guard).Nodup := eraseDups_nodup _
  apply pairs.imp_of_mem
  intro first second left right different equal
  exact different (functional formulas term guard first second left right equal)

/-- Executing the constructed finite substitution selects the complete logical name at every actual. -/
theorem rename_actual [DecidableEq Formula] (formulas : Formulas Formula) (term : Language.Term (Label Formula))
    (guard : Guard Formula) (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard) :
    renameName (names formulas term guard)
      (logicalName formulas (observe term) (sameShape formulas (observe term) []) guard actual) =
      logicalName formulas (observe term) (sameTerm formulas term []) guard actual :=
  FreshEnvironment.rename_of_member _ (keys_unique formulas term guard) _ _ (name_member formulas term guard actual member)

/-- Pull back any complete value environment along the actual source identity map. -/
theorem environment_actual [DecidableEq Formula] (model : FullSyntax.Interpretation Value)
    (formulas : Formulas Formula) (term : Language.Term (Label Formula)) (guard : Guard Formula)
    (env : Name → Value) (actual : Actual Formula) (member : actual ∈ actuals (observe term) guard) :
    SourceFormula.renamedEnvironment model env (names formulas term guard)
      (logicalName formulas (observe term) (sameShape formulas (observe term) []) guard actual) =
      env (logicalName formulas (observe term) (sameTerm formulas term []) guard actual) := by
  rw [FreshEnvironment.environment_names model env _ (keys_unique formulas term guard), rename_actual formulas term guard actual member]

private theorem complete_class_name [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (left : first ∈ actuals (observe term) guard) (right : second ∈ actuals (observe term) guard)
    (same : representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) first =
      representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) second) : first.name = second.name := by
  apply (ActualQuotient.actual_labels_equal term guard first second left right _).1
  rw [← ActualQuotient.complete_representative_same formulas term guard first left,
    ← ActualQuotient.complete_representative_same formulas term guard second right, same]

/-- Complete identity merging cannot create a name conflict for an unallocated sparse actual. -/
theorem complete_count_le_one [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard)
    (absent : (allocated formulas (observe term) (sameShape formulas (observe term) []) guard).lookup
      (representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual) = none) :
    (values (observe term) (sameTerm formulas term []) guard).countP (fun value => decide (value.2 = actual.name)) ≤ 1 := by
  let key := (representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual, actual.name)
  have unique : (values (observe term) (sameTerm formulas term []) guard).Nodup := eraseDups_nodup _
  have bound := List.Nodup.length_le_of_subset (unique.filter (fun value => decide (value.2 = actual.name)))
    (l₂ := [key]) (by
      intro row present
      obtain ⟨valueMember, nameEq⟩ := List.mem_filter.mp present
      simp only [values, List.mem_eraseDups] at valueMember
      obtain ⟨other, otherMember, rowEq⟩ := List.mem_map.mp valueMember
      subst row
      have equalName : other.name = actual.name := by simpa using nameEq
      have sparse := unallocated_same_class formulas (observe term) (sameShape formulas (observe term) []) guard
        actual other member otherMember absent equalName.symm
      have complete := ActualQuotient.sparse_classes_refine_complete formulas term guard actual other member otherMember sparse
      simp only [List.mem_singleton]
      exact Prod.ext complete.symm equalName)
  simpa only [List.countP_eq_length_filter, List.length_singleton] using bound

/-- A sparse actual without a generated declaration also needs no complete generated declaration. -/
theorem unallocated_complete [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard)
    (absent : (allocated formulas (observe term) (sameShape formulas (observe term) []) guard).lookup
      (representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual) = none) :
    (allocated formulas (observe term) (sameTerm formulas term []) guard).lookup
      (representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual) = none := by
  cases found : (allocated formulas (observe term) (sameTerm formulas term []) guard).lookup
      (representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual) with
  | none => rfl
  | some binding =>
      have row := lookup_member _ _ _ found
      have conflict : (representative (observe term) (sameTerm formulas term []) (actuals (observe term) guard) actual, binding.2) ∈
          conflicts (observe term) (sameTerm formulas term []) guard := by
        rw [← allocated_sources formulas (observe term) (sameTerm formulas term []) guard]
        exact List.mem_map.mpr ⟨_, row, rfl⟩
      have parts := List.mem_filter.mp conflict
      have valueMember := parts.1
      simp only [values, List.mem_eraseDups] at valueMember
      obtain ⟨other, otherMember, pairEq⟩ := List.mem_map.mp valueMember
      have nameEq := complete_class_name formulas term guard other actual otherMember member (congrArg Prod.fst pairEq)
      have original : binding.2 = actual.name := (congrArg Prod.snd pairEq).symm.trans nameEq
      have count : 1 < (values (observe term) (sameTerm formulas term []) guard).countP (fun value => decide (value.2 = actual.name)) := by
        simpa [original] using parts.2
      have bound := complete_count_le_one formulas term guard actual member absent
      omega

/-- Original logical names remain original when complete identity information removes sparse classes. -/
theorem unallocated_fixed [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals (observe term) guard)
    (absent : (allocated formulas (observe term) (sameShape formulas (observe term) []) guard).lookup
      (representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual) = none) :
    logicalName formulas (observe term) (sameTerm formulas term []) guard actual = actual.name := by
  simp [logicalName, unallocated_complete formulas term guard actual member absent]

/-- The executed identity quotient fixes every name in the source allocator's original avoid set. -/
theorem used_fixed [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (name : Name)
    (used : name ∈ usedNames formulas (observe term) guard) : renameName (names formulas term guard) name = name := by
  by_cases present : name ∈ (names formulas term guard).map Prod.fst
  · obtain ⟨pair, member, key⟩ := List.mem_map.mp present
    simp only [names, List.mem_eraseDups] at member
    obtain ⟨actual, actualMember, pairEq⟩ := List.mem_map.mp member
    subst pair
    dsimp only at key
    cases found : (allocated formulas (observe term) (sameShape formulas (observe term) []) guard).lookup
        (representative (observe term) (sameShape formulas (observe term) []) (actuals (observe term) guard) actual) with
    | none =>
        have original : actual.name = name := by simpa [logicalName, found] using key
        have selected := rename_actual formulas term guard actual actualMember
        rw [key, unallocated_fixed formulas term guard actual actualMember found, original] at selected
        exact selected
    | some binding =>
        have fresh : binding.1 = name := by simpa [logicalName, found] using key
        have avoided := SourceActuals.allocated_avoids formulas (observe term) (sameShape formulas (observe term) []) guard _ _ _
          (lookup_member _ _ _ found)
        exact False.elim (avoided (fresh ▸ used))
  · exact FormulaBinders.rename_absent _ _ present

end MicroCFTA.SourceIdentityMap
