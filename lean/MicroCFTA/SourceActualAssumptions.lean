import MicroCFTA.SourceResolvedTables

/-!
# Meaning of renamed source actual assumptions

The source resolves an actual refinement by replacing the value name with its
logical identity. Equal ambient free values and corresponding actual values
give equivalent assumptions under the complete repaired formula semantics.
-/
namespace MicroCFTA.SourceActualAssumptions
open FullSyntax FormulaSubstitution SourceFormula FreshEnvironment

/-- One resolved actual assumption agrees across corresponding logical identities. -/
theorem assumption_equivalent (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (first second : Name → Value)
    (oldName newName : Name) (refinement : Formula)
    (ambient : FormulaSemantics.Agree (formulaNames refinement) first second)
    (actual : first oldName = second newName) :
    Holds model first (substitute [(SourceGuards.valueName, oldName)] refinement) ↔
      Holds model second (substitute [(SourceGuards.valueName, newName)] refinement) := by
  rw [substitute_semantics model nullary first, substitute_semantics model nullary second]
  apply FormulaSemantics.formula_ext
  intro name member
  change renamedEnvironment model first [(SourceGuards.valueName, oldName)] name =
    renamedEnvironment model second [(SourceGuards.valueName, newName)] name
  rw [environment_names model first _ (by simp) name, environment_names model second _ (by simp) name]
  by_cases value : name = SourceGuards.valueName
  · simpa [renameName, value] using actual
  · simpa [renameName, value] using ambient name member

/-- The actual field rebuilt by source table renaming has the old field's meaning under corresponding values. -/
theorem resolved_assumption_equivalent (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (first second : Name → Value)
    (renamed : List (Name × Name)) (actualRefinement : Formula) (resolved : SourceGuards.Resolved Formula)
    (original : resolved.actualAssumption = substitute [(SourceGuards.valueName, resolved.replacement.2)] actualRefinement)
    (ambient : FormulaSemantics.Agree (formulaNames actualRefinement) first second)
    (actual : first resolved.replacement.2 = second (renameName renamed resolved.replacement.2)) :
    Holds model first resolved.actualAssumption ↔
      Holds model second (SourceResolvedTables.renameResolved operations renamed actualRefinement resolved).actualAssumption := by
  rw [original]
  exact assumption_equivalent model nullary first second _ _ actualRefinement ambient actual

/-- The concrete source resolver gives the expected original actual-assumption field. -/
theorem resolve_actual_assumption (observed : SourceGuards.Observations Formula)
    (fresh : List (SourceGuards.Path × (Name × Name))) (unknown : List SourceGuards.Path)
    (substitution : SourceGuards.Substitution) (actual : SourceGuards.Observed Formula)
    (resolved : SourceGuards.Resolved Formula)
    (atActual : observed substitution.actual = some actual)
    (success : SourceGuards.resolve operations observed fresh unknown substitution = some resolved) :
    resolved.actualAssumption = substitute [(SourceGuards.valueName, resolved.replacement.2)] actual.refinement := by
  obtain ⟨_, formal, _, atFormal⟩ := SourceActuals.resolve_exists operations observed fresh unknown substitution resolved success
  simp [SourceGuards.resolve, atActual, atFormal] at success
  subst resolved
  rfl

/-- The full source field transport is semantic, even when capture avoidance changes bound names. -/
theorem resolve_tables_assumption (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (firstEnv secondEnv : Name → Value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (substitution : SourceGuards.Substitution)
    (actual : SourceGuards.Observed Formula) (resolved : SourceGuards.Resolved Formula)
    (actualRead : substitution.actual ∈ SourceGuards.sensitive guard)
    (formalRead : substitution.formal ∈ SourceGuards.sensitive guard)
    (atActual : first substitution.actual = some actual)
    (success : SourceGuards.resolve operations first
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).1
      (SourceGuards.substitutionValues operations first (SourceObservations.sameShape operations first []) guard).2
      substitution = some resolved)
    (ambient : FormulaSemantics.Agree (formulaNames actual.refinement) firstEnv secondEnv)
    (actualValue : firstEnv resolved.replacement.2 =
      secondEnv (renameName (SourceFreshTables.tableRenaming operations guard first second) resolved.replacement.2)) :
    ∃ next,
      SourceGuards.resolve operations second
        (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).1
        (SourceGuards.substitutionValues operations second (SourceObservations.sameShape operations second []) guard).2
        substitution = some next ∧
      (Holds model firstEnv resolved.actualAssumption ↔ Holds model secondEnv next.actualAssumption) := by
  refine ⟨_, ?_, resolved_assumption_equivalent model nullary firstEnv secondEnv _ actual.refinement resolved
    (resolve_actual_assumption first _ _ substitution actual resolved atActual success) ambient actualValue⟩
  rw [SourceResolvedTables.resolve_tables operations guard first second reads substitution actual actualRead formalRead atActual, success]
  rfl

end MicroCFTA.SourceActualAssumptions
