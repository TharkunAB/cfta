import MicroCFTA.SourceHoldsQueries

/-!
# Exact logical-name lookup for actual positions

The source first allocates names by representative path, then copies the
optional declaration to every actual path. These proofs connect both lookups
without assuming unique constructor names.
-/
namespace MicroCFTA.SourceLogicalNames
open SourceGuards SourceObservations

/-- A successful first-match lookup returns an actual table row. -/
theorem lookup_member {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (entries : List (Key × Value)) (key : Key) (value : Value) (found : entries.lookup key = some value) :
    (key, value) ∈ entries := by
  obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp found
  rw [same]
  simp

/-- A functional table returns the value of each member, even if it repeats a row. -/
theorem lookup_of_member {Key Value : Type} [BEq Key] [LawfulBEq Key]
    (entries : List (Key × Value)) (key : Key) (value : Value) (member : (key, value) ∈ entries)
    (functional : ∀ other, (key, other) ∈ entries → other = value) : entries.lookup key = some value := by
  cases found : entries.lookup key with
  | none =>
      have impossible := (List.lookup_eq_none_iff.mp found) (key, value) member
      simp at impossible
  | some other => rw [functional other (lookup_member entries key other found)]

/-- Two actual records at one observed path have the same complete record fields. -/
theorem actual_target_unique (observed : Observations Formula) (guard : Guard Formula)
    (first second : Actual Formula) (left : first ∈ actuals observed guard) (right : second ∈ actuals observed guard)
    (same : first.target = second.target) : first = second := by
  obtain ⟨a, ha, na, ra⟩ := ActualQuotient.actual_observed observed guard first left
  obtain ⟨b, hb, nb, rb⟩ := ActualQuotient.actual_observed observed guard second right
  rw [same] at ha
  have equal : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  cases first; cases second
  simp_all

/-- Copying optional declarations to actual paths retains the allocation lookup exactly. -/
theorem copied_lookup [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals observed guard) :
    (substitutionValues formulas observed sameAt guard).1.lookup actual.target =
      (allocated formulas observed sameAt guard).lookup (representative observed sameAt (actuals observed guard) actual) := by
  let binding := fun current : Actual Formula =>
    (allocated formulas observed sameAt guard).lookup (representative observed sameAt (actuals observed guard) current)
  change ((actuals observed guard).filterMap fun current => (binding current).map (fun value => (current.target, value))).lookup actual.target = binding actual
  cases chosen : binding actual with
  | none =>
      apply List.lookup_eq_none_iff.mpr
      intro pair present
      obtain ⟨current, currentMember, output⟩ := List.mem_filterMap.mp present
      cases selected : binding current with
      | none => simp [selected] at output
      | some value =>
          have pairEqual : (current.target, value) = pair := by simpa [selected] using output
          subst pair
          by_cases same : actual.target = current.target
          · have equal := actual_target_unique observed guard actual current member currentMember same
            simp [← equal, chosen] at selected
          · simpa using same
  | some value =>
      apply lookup_of_member
      · exact List.mem_filterMap.mpr ⟨actual, member, by simp [chosen]⟩
      · intro other present
        obtain ⟨current, currentMember, output⟩ := List.mem_filterMap.mp present
        cases selected : binding current with
        | none => simp [selected] at output
        | some currentValue =>
            have pairEqual : (current.target, currentValue) = (actual.target, other) := by simpa [selected] using output
            have equal := actual_target_unique observed guard current actual currentMember member (congrArg Prod.fst pairEqual)
            have valueEqual : currentValue = value := Option.some.inj (selected.symm.trans (equal ▸ chosen))
            exact (congrArg Prod.snd pairEqual).symm.trans valueEqual

/-- The logical identity of an actual uses its allocated name, or its original name when no declaration exists. -/
def logicalName [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) (actual : Actual Formula) : Name :=
  (((allocated formulas observed sameAt guard).lookup
    (representative observed sameAt (actuals observed guard) actual)).map Prod.fst).getD actual.name

/-- The public per-path table selects exactly the same logical identity. -/
theorem logicalName_copied [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals observed guard) :
    (((substitutionValues formulas observed sameAt guard).1.lookup actual.target).map Prod.fst).getD actual.name =
      logicalName formulas observed sameAt guard actual := by
  rw [copied_lookup formulas observed sameAt guard actual member]
  rfl

/-- A list with unique mapped values has no two different members with one mapped value. -/
theorem mapped_unique {α β : Type} (items : List α) (field : α → β)
    (unique : (items.map field).Nodup) (first second : α)
    (left : first ∈ items) (right : second ∈ items) (same : field first = field second) : first = second := by
  induction items with
  | nil => simp at left
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp left with rfl | leftRest
      · rcases List.mem_cons.mp right with rfl | rightRest
        · rfl
        · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨second, rightRest, rfl⟩))
      · rcases List.mem_cons.mp right with rfl | rightRest
        · exact False.elim (unique.1 (same ▸ List.mem_map.mpr ⟨first, leftRest, rfl⟩))
        · exact ih unique.2 leftRest rightRest

/-- Projecting the allocation rows recovers every conflicting representative and original name. -/
theorem allocated_sources [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    (allocated formulas observed sameAt guard).map (fun row => (row.1, row.2.2)) = conflicts observed sameAt guard := by
  unfold allocated
  simp only [List.map_map, Function.comp_def]
  change ((conflicts observed sameAt guard).zip (freshNames (usedNames formulas observed guard)
    (conflicts observed sameAt guard).length)).map Prod.fst = _
  apply List.map_fst_zip
  simp [SourceActuals.fresh_length]

/-- Projecting the allocated names recovers the complete source fresh stream. -/
theorem allocated_fresh [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) :
    (allocated formulas observed sameAt guard).map (fun row => row.2.1) =
      freshNames (usedNames formulas observed guard) (conflicts observed sameAt guard).length := by
  unfold allocated
  simp only [List.map_map, Function.comp_def]
  apply List.map_snd_zip
  simp [SourceActuals.fresh_length]

/-- Different allocated source rows always have different logical names. -/
theorem allocated_name_unique [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula)
    (first second : Path × (Name × Name))
    (left : first ∈ allocated formulas observed sameAt guard) (right : second ∈ allocated formulas observed sameAt guard)
    (same : first.2.1 = second.2.1) : first = second := by
  apply mapped_unique _ (fun row => row.2.1) _ first second left right same
  rw [allocated_fresh]
  exact SourceActuals.fresh_nodup _ _

/-- Every actual contributes its representative and original name to the source value set. -/
theorem actual_value [DecidableEq Formula] (observed : Observations Formula) (sameAt : Path → Path → Option Bool)
    (guard : Guard Formula) (actual : Actual Formula) (member : actual ∈ actuals observed guard) :
    (representative observed sameAt (actuals observed guard) actual, actual.name) ∈ values observed sameAt guard := by
  simp only [values, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨actual, member, rfl⟩

/-- An actual without an allocated declaration is not in the source conflict list. -/
theorem unallocated_not_conflicting [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) (actual : Actual Formula)
    (absent : (allocated formulas observed sameAt guard).lookup
      (representative observed sameAt (actuals observed guard) actual) = none) :
    (representative observed sameAt (actuals observed guard) actual, actual.name) ∉ conflicts observed sameAt guard := by
  intro member
  rw [← allocated_sources formulas observed sameAt guard] at member
  obtain ⟨row, present, same⟩ := List.mem_map.mp member
  have impossible := (List.lookup_eq_none_iff.mp absent) row present
  have equal : row.1 = representative observed sameAt (actuals observed guard) actual := congrArg Prod.fst same
  simp [equal] at impossible

/-- Equal original names without allocation can belong to only one representative class. -/
theorem unallocated_same_class [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) (first second : Actual Formula)
    (left : first ∈ actuals observed guard) (right : second ∈ actuals observed guard)
    (absent : (allocated formulas observed sameAt guard).lookup
      (representative observed sameAt (actuals observed guard) first) = none)
    (sameName : first.name = second.name) :
    representative observed sameAt (actuals observed guard) first = representative observed sameAt (actuals observed guard) second := by
  by_cases equal : representative observed sameAt (actuals observed guard) first = representative observed sameAt (actuals observed guard) second
  · exact equal
  · have different : (representative observed sameAt (actuals observed guard) first, first.name) ≠
        (representative observed sameAt (actuals observed guard) second, second.name) := fun same => equal (congrArg Prod.fst same)
    have count := NoConflictKnown.countP_two (values observed sameAt guard) _ _ (fun value => decide (value.2 = first.name))
      (actual_value observed sameAt guard first left) (actual_value observed sameAt guard second right) different
      (by simp) (by simp [sameName])
    apply False.elim
    apply unallocated_not_conflicting formulas observed sameAt guard first absent
    exact List.mem_filter.mpr ⟨actual_value observed sameAt guard first left, by simp; omega⟩

/-- Every actual's original name is excluded from allocation. -/
theorem actual_name_used (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (actual : Actual Formula) (member : actual ∈ actuals observed guard) : actual.name ∈ usedNames formulas observed guard := by
  obtain ⟨value, found, name, _⟩ := ActualQuotient.actual_observed observed guard actual member
  rw [← name]
  exact SourceResolvedTables.used_at formulas observed guard actual.target value
    (SourceReadAgreement.sensitive_requested guard _
      (SourceIdentityReads.actual_sensitive guard _ (SourceIdentityReads.actual_requested observed guard actual member))) found

/-- The executed source logical-name allocation is injective on representative classes. -/
theorem logicalName_class [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula) (first second : Actual Formula)
    (left : first ∈ actuals observed guard) (right : second ∈ actuals observed guard)
    (same : logicalName formulas observed sameAt guard first = logicalName formulas observed sameAt guard second) :
    representative observed sameAt (actuals observed guard) first = representative observed sameAt (actuals observed guard) second := by
  cases a : (allocated formulas observed sameAt guard).lookup (representative observed sameAt (actuals observed guard) first) with
  | none =>
      cases b : (allocated formulas observed sameAt guard).lookup (representative observed sameAt (actuals observed guard) second) with
      | none =>
          exact unallocated_same_class formulas observed sameAt guard first second left right a
            (by simpa [logicalName, a, b] using same)
      | some declaration =>
          have equal : first.name = declaration.1 := by simpa [logicalName, a, b] using same
          have avoided := SourceActuals.allocated_avoids formulas observed sameAt guard _ declaration.1 declaration.2
            (lookup_member _ _ _ b)
          exact False.elim (avoided (equal ▸ actual_name_used formulas observed guard first left))
  | some declaration =>
      cases b : (allocated formulas observed sameAt guard).lookup (representative observed sameAt (actuals observed guard) second) with
      | none =>
          have equal : declaration.1 = second.name := by simpa [logicalName, a, b] using same
          have avoided := SourceActuals.allocated_avoids formulas observed sameAt guard _ declaration.1 declaration.2
            (lookup_member _ _ _ a)
          exact False.elim (avoided (equal ▸ actual_name_used formulas observed guard second right))
      | some other =>
          have equal : declaration.1 = other.1 := by simpa [logicalName, a, b] using same
          have rows := allocated_name_unique formulas observed sameAt guard _ _
            (lookup_member _ _ _ a) (lookup_member _ _ _ b) equal
          exact congrArg Prod.fst rows

/-- Equal sparse logical names denote the same complete actual term. -/
theorem sparse_name_same_term [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (left : first ∈ actuals (observe term) guard) (right : second ∈ actuals (observe term) guard)
    (same : logicalName formulas (observe term) (sameShape formulas (observe term) []) guard first =
      logicalName formulas (observe term) (sameShape formulas (observe term) []) guard second) :
    Language.Term.atPath term first.target = Language.Term.atPath term second.target :=
  ActualQuotient.sparse_classes_refine_terms formulas term guard first second left right
    (logicalName_class formulas (observe term) _ guard first second left right same)

/-- The target logical name is constant on each sparse logical-name class. -/
theorem sparse_name_complete_name [DecidableEq Formula] (formulas : Formulas Formula)
    (term : Language.Term (Label Formula)) (guard : Guard Formula) (first second : Actual Formula)
    (left : first ∈ actuals (observe term) guard) (right : second ∈ actuals (observe term) guard)
    (same : logicalName formulas (observe term) (sameShape formulas (observe term) []) guard first =
      logicalName formulas (observe term) (sameShape formulas (observe term) []) guard second) :
    logicalName formulas (observe term) (sameTerm formulas term []) guard first =
      logicalName formulas (observe term) (sameTerm formulas term []) guard second := by
  have trees := sparse_name_same_term formulas term guard first second left right same
  have labels := ActualQuotient.actual_labels_equal term guard first second left right trees
  have representatives := ActualQuotient.complete_representative_canonical formulas term guard first second left right trees
  simp only [logicalName, representatives, labels.1]

end MicroCFTA.SourceLogicalNames
