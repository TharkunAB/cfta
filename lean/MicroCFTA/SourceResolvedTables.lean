import MicroCFTA.SourceFreshTables

/-!
# Resolve substitutions through the constructed source name map

Resolution keeps literal symbol substitutions separate from solver names.
The per-entry theorem includes the rebuilt actual assumption. The list
theorem preserves successful scope length, order, metadata, and failure.
-/
namespace MicroCFTA.SourceResolvedTables
open SourceGuards SourceObservations SourceReadAgreement SourceFreshTables FormulaSubstitution FreshEnvironment

/-- Every observed name at a requested path belongs to the actual fresh-name avoid list. -/
theorem used_at (formulas : Formulas Formula) (observed : Observations Formula) (guard : Guard Formula)
    (path : Path) (value : Observed Formula) (requested : path ∈ paths guard)
    (found : observed path = some value) : value.name ∈ usedNames formulas observed guard := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨path, ?_, ?_⟩
  · simpa [orderedPaths] using requested
  · simp [found]

/-- A fresh spelling map leaves every original used name fixed. -/
theorem fixed_used [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (name : Name) (used : name ∈ usedNames formulas first guard) :
    renameName (tableRenaming formulas guard first second) name = name := by
  apply FormulaBinders.rename_absent
  unfold tableRenaming
  rw [fresh_keys]
  exact fun member => SourceActuals.fresh_avoids _ _ name member used

/-- Rebuild the exact resolved record from its original actual refinement and renamed logical identity. -/
def renameResolved (formulas : Formulas Formula) (renamed : List (Name × Name)) (actualRefinement : Formula)
    (resolved : Resolved Formula) : Resolved Formula :=
  ⟨(resolved.replacement.1, renameName renamed resolved.replacement.2), resolved.symbolReplacement,
   formulas.substitute [(valueName, renameName renamed resolved.replacement.2)] actualRefinement,
   resolved.declaration.map (fun binding => (renameName renamed binding.1, binding.2)), resolved.identityKnown⟩

/-- Source resolution commutes with declaration renaming when the ambient actual name remains fixed. -/
theorem resolve_map (formulas : Formulas Formula) (first second : Observations Formula)
    (fresh : List (Path × (Name × Name))) (unknown : List Path) (renamed : List (Name × Name))
    (substitution : Substitution) (actual : Observed Formula)
    (firstActual : first substitution.actual = some actual) (secondActual : second substitution.actual = some actual)
    (formal : first substitution.formal = second substitution.formal)
    (fixed : renameName renamed actual.name = actual.name) :
    resolve formulas second (fresh.map (renameEntry renamed)) unknown substitution =
      (resolve formulas first fresh unknown substitution).map (renameResolved formulas renamed actual.refinement) := by
  cases form : first substitution.formal with
  | none => simp [resolve, firstActual, secondActual, ← formal, form]
  | some value =>
      cases declaration : fresh.lookup substitution.actual <;>
        simp [resolve, firstActual, secondActual, ← formal, form, lookup_rename, declaration, renameResolved, fixed]

/-- The concrete two observation tables yield exactly the renamed source resolved record. -/
theorem resolve_tables [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second)
    (substitution : Substitution) (actual : Observed Formula)
    (actualRead : substitution.actual ∈ sensitive guard) (formalRead : substitution.formal ∈ sensitive guard)
    (found : first substitution.actual = some actual) :
    resolve formulas second (substitutionValues formulas second (sameShape formulas second []) guard).1
      (substitutionValues formulas second (sameShape formulas second []) guard).2 substitution =
    (resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
      (substitutionValues formulas first (sameShape formulas first []) guard).2 substitution).map
        (renameResolved formulas (tableRenaming formulas guard first second) actual.refinement) := by
  rw [tables_rename formulas guard first second reads]
  apply resolve_map formulas first second _ _ _ substitution actual found
  · exact (reads.symbols _ actualRead).symm.trans found
  · exact reads.symbols _ formalRead
  · exact fixed_used formulas guard first second actual.name
      (used_at formulas first guard _ actual (sensitive_requested guard _ actualRead) found)

/-- All non-formula fields preserve the exact source position and identity metadata. -/
def Aligned (renamed : List (Name × Name)) (first second : Resolved Formula) : Prop :=
  second.replacement = (first.replacement.1, renameName renamed first.replacement.2) ∧
  second.symbolReplacement = first.symbolReplacement ∧
  second.declaration = first.declaration.map (fun binding => (renameName renamed binding.1, binding.2)) ∧
  second.identityKnown = first.identityKnown

/-- Missing results agree; successful results satisfy the specified relation. -/
def OptionRel (relation : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some first, some second => relation first second
  | _, _ => False

/-- Single-entry resolution preserves failure and every non-formula field without assuming either success. -/
theorem resolve_aligned [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) (substitution : Substitution)
    (actualRead : substitution.actual ∈ sensitive guard) (formalRead : substitution.formal ∈ sensitive guard) :
    OptionRel (Aligned (tableRenaming formulas guard first second))
      (resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
        (substitutionValues formulas first (sameShape formulas first []) guard).2 substitution)
      (resolve formulas second (substitutionValues formulas second (sameShape formulas second []) guard).1
        (substitutionValues formulas second (sameShape formulas second []) guard).2 substitution) := by
  cases found : first substitution.actual with
  | none =>
      have absent : second substitution.actual = none := (reads.symbols _ actualRead).symm.trans found
      simp [resolve, found, absent, OptionRel]
  | some actual =>
      rw [resolve_tables formulas guard first second reads substitution actual actualRead formalRead found]
      cases resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
          (substitutionValues formulas first (sameShape formulas first []) guard).2 substitution <;>
        simp [OptionRel, Aligned, renameResolved]

/-- Every resolved scope preserves ordered metadata and the exact failure boundary. -/
theorem resolveMany_aligned [DecidableEq Formula] (formulas : Formulas Formula) (guard : Guard Formula)
    (first second : Observations Formula) (reads : Reads guard first second) (additions : List Substitution)
    (requested : ∀ entry ∈ additions, entry.actual ∈ sensitive guard ∧ entry.formal ∈ sensitive guard) :
    OptionRel (Language.All₂ (Aligned (tableRenaming formulas guard first second)))
      (resolveMany formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
        (substitutionValues formulas first (sameShape formulas first []) guard).2 additions)
      (resolveMany formulas second (substitutionValues formulas second (sameShape formulas second []) guard).1
        (substitutionValues formulas second (sameShape formulas second []) guard).2 additions) := by
  induction additions with
  | nil => exact Language.All₂.nil
  | cons entry rest ih =>
      have positions := requested entry (by simp)
      have head := resolve_aligned formulas guard first second reads entry positions.1 positions.2
      have tail := ih (fun other member => requested other (by simp [member]))
      simp only [resolveMany]
      cases a : resolve formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
          (substitutionValues formulas first (sameShape formulas first []) guard).2 entry <;>
        cases b : resolve formulas second (substitutionValues formulas second (sameShape formulas second []) guard).1
          (substitutionValues formulas second (sameShape formulas second []) guard).2 entry <;>
        cases c : resolveMany formulas first (substitutionValues formulas first (sameShape formulas first []) guard).1
          (substitutionValues formulas first (sameShape formulas first []) guard).2 rest <;>
        cases d : resolveMany formulas second (substitutionValues formulas second (sameShape formulas second []) guard).1
          (substitutionValues formulas second (sameShape formulas second []) guard).2 rest <;>
        simp_all [OptionRel]
      apply Language.All₂.cons <;> assumption

end MicroCFTA.SourceResolvedTables
