import MicroCFTA.SourceContractNames

/-!
# Exact source relational contract formulas

The formula contains one value-substituted refinement per positional formal
and one alias for each repeated path after its first occurrence. This proof
retains both parts of the source construction.
-/
namespace MicroCFTA.SourceContractSemantics
open FullSyntax FormulaSubstitution SourceFormula SourceScopeStack

private theorem conjunction_ext (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (first second : Name → Value) (parts : List Formula)
    (same : ∀ part ∈ parts, Holds model first part ↔ Holds model second part) :
    Holds model first (operations.conjunction parts) ↔ Holds model second (operations.conjunction parts) := by
  rw [conjunction_semantics model laws, conjunction_semantics model laws]
  exact ⟨fun all part member => (same part member).mp (all part member),
    fun all part member => (same part member).mpr (all part member)⟩

/-- Replacing the value variable uses only the original free values and its positional formal. -/
theorem value_formula_ext (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (first second : Name → Value) (formal : Name) (formula : Formula)
    (names : FormulaSemantics.Agree (formulaNames formula) first second) (value : first formal = second formal) :
    Holds model first (operations.substitute [(SourceGuards.valueName, formal)] formula) ↔
      Holds model second (operations.substitute [(SourceGuards.valueName, formal)] formula) := by
  rw [show operations.substitute = SourceFormula.substitute from rfl, substitute_semantics model nullary, substitute_semantics model nullary]
  apply FormulaSemantics.formula_ext
  intro name member
  change renamedEnvironment model first [(SourceGuards.valueName, formal)] name =
    renamedEnvironment model second [(SourceGuards.valueName, formal)] name
  simp only [SourceScopeEnvironment.environment_cons]
  split
  · exact names name member
  · split
    · exact value
    · exact names name member

/-- Contract truth depends on all supplied refinements and every generated positional value. -/
theorem contract_ext (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (laws : FormulaSimplify.RelationLaws model) (first second : Name → Value)
    (targets : List SourceGuards.Path) (values : List (SourceGuards.Observed Formula))
    (refinements : ∀ value ∈ values, FormulaSemantics.Agree (formulaNames value.refinement) first second)
    (formals : ∀ index < targets.length, first (SourceGuards.contractName index) = second (SourceGuards.contractName index)) :
    Holds model first (SourceGuards.contract operations targets values).2 ↔
      Holds model second (SourceGuards.contract operations targets values).2 := by
  unfold SourceGuards.contract
  apply conjunction_ext model laws
  intro formula member
  rcases List.mem_append.mp member with refinement | alias
  · obtain ⟨pair, paired, rfl⟩ := List.mem_map.mp refinement
    have positions := List.of_mem_zip paired
    obtain ⟨index, bounded, formal⟩ := List.mem_map.mp positions.1
    apply value_formula_ext model nullary _ _ _ _ (refinements pair.2 positions.2)
    rw [← formal]
    exact formals index (List.mem_range.mp bounded)
  · obtain ⟨pair, paired, found⟩ := List.mem_filterMap.mp alias
    have positions := List.of_mem_zip paired
    obtain ⟨index, bounded, formal⟩ := List.mem_map.mp positions.2
    cases chosen : (targets.zip ((List.range targets.length).map SourceGuards.contractName)).lookup pair.1 with
    | none => simp [chosen] at found
    | some initial =>
        by_cases identity : initial = pair.2
        · simp [chosen, identity] at found
        · have output : operations.equalNames pair.2 initial = formula := by simpa [chosen, identity] using found
          subst formula
          have initialMember := SourceGuards.contract_first_name targets pair.1 initial chosen
          obtain ⟨firstIndex, firstBound, firstName⟩ := List.mem_map.mp (List.of_mem_zip initialMember).2
          rw [alias_semantics, alias_semantics, ← formal, ← firstName,
            formals index (List.mem_range.mp bounded), formals firstIndex (List.mem_range.mp firstBound)]

end MicroCFTA.SourceContractSemantics
