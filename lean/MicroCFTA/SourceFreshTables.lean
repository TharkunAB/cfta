import MicroCFTA.FreshEnvironment

/-!
# Exact fresh-name correspondence of equal guard signatures

The same source conflict entries can allocate different fresh strings. Their
corresponding finite streams define the exact renaming of every allocated and
per-path declaration. Missing entries stay missing.
-/
namespace MicroCFTA.SourceFreshTables
open SourceGuards SourceObservations SourceReadAgreement FormulaSubstitution FreshEnvironment

/-- Rename only the allocated solver name; retain its actual path and declared sort name. -/
def renameEntry (renamed : List (Name × Name)) (entry : Path × (Name × Name)) : Path × (Name × Name) :=
  (entry.1, renameName renamed entry.2.1, entry.2.2)

/-- The source conflict count determines the corresponding fresh-name stream positions. -/
def tableRenaming [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) : List (Name × Name) :=
  freshRenaming (usedNames formulas first guard) (usedNames formulas second guard)
    (conflicts first (sameShape formulas first []) guard).length

/-- Exact source allocation rows differ only by the constructed fresh-name map. -/
theorem allocated_rename [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    allocated formulas second (sameShape formulas second []) guard =
      (allocated formulas first (sameShape formulas first []) guard).map
        (renameEntry (tableRenaming formulas guard first second)) := by
  have conflictsSame := SourceIdentityReads.conflicts_reads formulas guard first second reads
  have streams := fresh_map_stream (usedNames formulas first guard) (usedNames formulas second guard)
    (conflicts first (sameShape formulas first []) guard).length
  unfold allocated
  rw [← conflictsSame]
  dsimp only
  rw [← streams, List.zip_map_right, List.map_map, List.map_map]
  rfl

/-- Renaming declaration values commutes with first-match path lookup. -/
theorem lookup_rename (renamed : List (Name × Name)) (entries : List (Path × (Name × Name))) (path : Path) :
    (entries.map (renameEntry renamed)).lookup path =
      (entries.lookup path).map (fun binding => (renameName renamed binding.1, binding.2)) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, fresh, original⟩
      cases same : path == key <;> simp [renameEntry, List.lookup_cons, same, ih]

private theorem filterMap_congr (items : List α) (first second : α → Option β)
    (same : ∀ item ∈ items, first item = second item) : items.filterMap first = items.filterMap second := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.filterMap_cons, same item (by simp),
      ih (fun value member => same value (by simp [member]))]

/-- Every per-path source declaration follows the exact allocated fresh-name map. -/
theorem declarations_rename [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    (substitutionValues formulas second (sameShape formulas second []) guard).1 =
      ((substitutionValues formulas first (sameShape formulas first []) guard).1).map
        (renameEntry (tableRenaming formulas guard first second)) := by
  simp only [substitutionValues]
  rw [allocated_rename formulas guard first second reads]
  simp only [lookup_rename, Option.map_map, List.map_filterMap]
  have table := SourceIdentityReads.actuals_reads guard first second reads
  rw [← table]
  apply filterMap_congr
  intro actual member
  have representatives := SourceIdentityReads.representative_reads formulas guard first second reads actual member
  rw [← table] at representatives
  rw [← representatives]
  rfl

/-- The complete public table pair changes only declaration names; its ambiguity list is identical. -/
theorem tables_rename [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) :
    substitutionValues formulas second (sameShape formulas second []) guard =
      (((substitutionValues formulas first (sameShape formulas first []) guard).1).map
        (renameEntry (tableRenaming formulas guard first second)),
       (substitutionValues formulas first (sameShape formulas first []) guard).2) := by
  apply Prod.ext
  · exact declarations_rename formulas guard first second reads
  · exact (SourceIdentityReads.ambiguous_reads formulas guard first second reads).symm

/-- The generated name map has unique source keys and unique target values. -/
theorem renaming_unique [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) :
    ((tableRenaming formulas guard first second).map Prod.fst).Nodup ∧
      ((tableRenaming formulas guard first second).map Prod.snd).Nodup := by
  unfold tableRenaming
  rw [fresh_keys, fresh_targets]
  exact ⟨SourceActuals.fresh_nodup _ _, SourceActuals.fresh_nodup _ _⟩

end MicroCFTA.SourceFreshTables
