import MicroCFTA.SourceReadAgreement

/-!
# Actual-identity tables depend on the symbol-sensitive reads

Only fresh-name spelling also depends on constructor names at refinement-only
positions. This module isolates that dependency and removes it when no actual
name conflict needs a fresh declaration.
-/
namespace MicroCFTA.SourceIdentityReads
open SourceGuards SourceObservations SourceReadAgreement

private theorem filterMap_congr (items : List α) (first second : α → Option β)
    (same : ∀ item ∈ items, first item = second item) : items.filterMap first = items.filterMap second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.filterMap_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

private theorem find_congr (items : List α) (first second : α → Bool)
    (same : ∀ item ∈ items, first item = second item) : items.find? first = items.find? second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.find?_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

private theorem filter_congr (items : List α) (first second : α → Bool)
    (same : ∀ item ∈ items, first item = second item) : items.filter first = items.filter second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.filter_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

private theorem any_congr (items : List α) (first second : α → Bool)
    (same : ∀ item ∈ items, first item = second item) : items.any first = items.any second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.any_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

/-- Every actual position receives a full symbol-sensitive observation. -/
theorem actual_sensitive (guard : Guard Formula) (path : Path) (member : path ∈ actualPaths guard) :
    path ∈ sensitive guard := by
  cases guard with
  | top | bottom | same _ _ | entails _ _ | satisfies _ _ | holds _ _ => simp [actualPaths] at member
  | substitute additions inner =>
      simp only [actualPaths, List.mem_append] at member
      simp only [sensitive, List.mem_append]
      rcases member with added | nested
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp added
        exact Or.inl (List.mem_flatMap.mpr ⟨entry, present, by simp⟩)
      · exact Or.inr (actual_sensitive inner path nested)
  | not inner =>
      simp only [actualPaths] at member
      simpa only [sensitive] using actual_sensitive inner path member
  | and parts | or parts =>
      simp only [actualPaths] at member
      simp only [sensitive]
      obtain ⟨part, present, nested⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨part, present, actual_sensitive part path nested⟩
termination_by sizeOf guard

/-- An actual table never contains an unrequested path. -/
theorem actual_requested (observed : Observations Formula) (guard : Guard Formula) (actual : Actual Formula)
    (member : actual ∈ actuals observed guard) : actual.target ∈ actualPaths guard := by
  obtain ⟨target, present, found⟩ := List.mem_filterMap.mp member
  cases atTarget : observed target with
  | none => simp [atTarget] at found
  | some value =>
      simp only [atTarget, Option.map_some, Option.some.injEq] at found
      subst actual
      simpa [orderedPaths] using present

/-- Planned read agreement gives exact actual-table equality before representative search. -/
theorem actuals_reads (guard : Guard Formula) (first second : Observations Formula) (reads : Reads guard first second) :
    actuals first guard = actuals second guard := by
  unfold actuals
  apply filterMap_congr
  intro target member
  have requested : target ∈ actualPaths guard := by simpa [orderedPaths] using member
  rw [reads.symbols target (actual_sensitive guard target requested)]

/-- Read agreement preserves representative search, including leafness and the source equality callback. -/
theorem representative_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) (actual : Actual Formula)
    (member : actual ∈ actuals first guard) :
    representative first (sameShape formulas first []) (actuals first guard) actual =
      representative second (sameShape formulas second []) (actuals second guard) actual := by
  have own := reads.symbols actual.target (actual_sensitive guard actual.target (actual_requested first guard actual member))
  have table := actuals_reads guard first second reads
  unfold representative
  rw [← table]
  have search :
      (actuals first guard).find? (fun other =>
        decide (other.name = actual.name) && decide (other.refinement = actual.refinement) &&
          (decide (sameShape formulas first [] actual.target other.target = some true) ||
            (decide ((first actual.target).map Observed.leafness = some .leaf) &&
             decide ((first other.target).map Observed.leafness = some .leaf)))) =
      (actuals first guard).find? (fun other =>
        decide (other.name = actual.name) && decide (other.refinement = actual.refinement) &&
          (decide (sameShape formulas second [] actual.target other.target = some true) ||
            (decide ((second actual.target).map Observed.leafness = some .leaf) &&
             decide ((second other.target).map Observed.leafness = some .leaf)))) := by
    apply find_congr
    intro other present
    have otherRead := reads.symbols other.target (actual_sensitive guard other.target (actual_requested first guard other present))
    simp only [sameShape, own, otherRead]
    rfl
  rw [search]

/-- The representative/name list is independent of unobserved constructor names. -/
theorem values_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    values first (sameShape formulas first []) guard = values second (sameShape formulas second []) guard := by
  simp only [values]
  have table := actuals_reads guard first second reads
  apply congrArg List.eraseDups
  calc
    _ = (actuals first guard).map (fun actual =>
      (representative second (sameShape formulas second []) (actuals second guard) actual, actual.name)) := by
        apply List.map_congr_left
        intro actual member
        rw [representative_reads formulas guard first second reads actual member]
    _ = _ := by rw [table]

/-- Source conflict counts use only the symbol-sensitive actual observations. -/
theorem conflicts_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    conflicts first (sameShape formulas first []) guard = conflicts second (sameShape formulas second []) guard := by
  unfold conflicts
  rw [values_reads formulas guard first second reads]

/-- The source ambiguity set uses only the symbol-sensitive actual observations. -/
theorem ambiguous_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    ambiguous first (sameShape formulas first []) guard = ambiguous second (sameShape formulas second []) guard := by
  simp only [ambiguous]
  have table := actuals_reads guard first second reads
  rw [← table]
  congr 2
  apply filter_congr
  intro actual member
  have own := reads.symbols actual.target (actual_sensitive guard actual.target (actual_requested first guard actual member))
  apply any_congr
  intro other present
  have otherRead := reads.symbols other.target (actual_sensitive guard other.target (actual_requested first guard other present))
  simp only [sameShape, own, otherRead]
  rfl

/-- No conflict means no fresh declaration, regardless of the avoid set. -/
theorem allocated_no_conflict [DecidableEq Formula] (formulas : Formulas Formula) (observed : Observations Formula)
    (sameAt : Path → Path → Option Bool) (guard : Guard Formula)
    (noConflict : conflicts observed sameAt guard = []) : allocated formulas observed sameAt guard = [] := by
  simp [allocated, noConflict]

/-- With no name conflicts, equal source signatures give exactly equal actual tables. -/
theorem no_conflict_tables_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second)
    (noConflict : conflicts first (sameShape formulas first []) guard = []) :
    substitutionValues formulas first (sameShape formulas first []) guard =
      substitutionValues formulas second (sameShape formulas second []) guard := by
  have otherNoConflict : conflicts second (sameShape formulas second []) guard = [] :=
    (conflicts_reads formulas guard first second reads).symm.trans noConflict
  simp only [substitutionValues, allocated_no_conflict formulas first _ guard noConflict,
    allocated_no_conflict formulas second _ guard otherNoConflict, List.lookup_nil, Option.map_none,
    ambiguous_reads formulas guard first second reads]
  rw [actuals_reads guard first second reads]

/-- Full public guard evaluation is constant across a source signature without actual-name conflicts. -/
theorem no_conflict_signature_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (guard : Guard Formula) (first second : Observations Formula)
    (signatureEqual : signature guard first = signature guard second)
    (noConflict : conflicts first (sameShape formulas first []) guard = []) :
    evaluateGuardWithShape formulas solver first guard = evaluateGuardWithShape formulas solver second guard := by
  have reads := signature_reads guard first second signatureEqual
  unfold evaluateGuardWithShape evaluateGuardWithSame
  rw [no_conflict_tables_reads formulas guard first second reads noConflict]
  exact evaluate_reads formulas solver first second _ _ [] true guard reads

/-- Once the avoid list agrees, every actual table operation depends only on planned reads. -/
theorem tables_reads [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second)
    (avoid : usedNames formulas first guard = usedNames formulas second guard) :
    substitutionValues formulas first (sameShape formulas first []) guard =
      substitutionValues formulas second (sameShape formulas second []) guard := by
  have declarations : allocated formulas first (sameShape formulas first []) guard =
      allocated formulas second (sameShape formulas second []) guard := by
    unfold allocated
    rw [conflicts_reads formulas guard first second reads, avoid]
  unfold substitutionValues
  rw [declarations, ambiguous_reads formulas guard first second reads]
  dsimp only
  congr 1
  calc
    _ = (actuals first guard).filterMap (fun actual =>
      ((allocated formulas second (sameShape formulas second []) guard).lookup
        (representative second (sameShape formulas second []) (actuals second guard) actual)).map
          (fun binding => (actual.target, binding))) := by
      apply filterMap_congr
      intro actual member
      rw [representative_reads formulas guard first second reads actual member]
    _ = _ := by rw [actuals_reads guard first second reads]

/-- Full observation agreement at the requested paths preserves the complete fresh-name avoid list. -/
theorem usedNames_reads (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (full : ∀ path ∈ paths guard, first path = second path) :
    usedNames formulas first guard = usedNames formulas second guard := by
  unfold usedNames
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro target member
  rw [full target (by simpa [orderedPaths] using member)]

/-- Supplying exactly the full observations at all requested paths preserves public evaluation, including conflicts. -/
theorem requested_observations_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : SourceGuards.Entailment Formula) (guard : Guard Formula) (first second : Observations Formula)
    (full : ∀ path ∈ paths guard, first path = second path) :
    evaluateGuardWithShape formulas solver first guard = evaluateGuardWithShape formulas solver second guard := by
  have reads : Reads guard first second :=
    ⟨fun path member => congrArg (Option.map Observed.refinement) (full path member),
     fun path member => full path (sensitive_requested guard path member)⟩
  unfold evaluateGuardWithShape evaluateGuardWithSame
  rw [tables_reads formulas guard first second reads (usedNames_reads formulas guard first second full)]
  exact evaluate_reads formulas solver first second _ _ [] true guard reads

end MicroCFTA.SourceIdentityReads
