import MicroCFTA.SourceFormula

/-!
# Entailment under fresh names and actual-value identification

A positive entailment remains valid after name identification. A failed
entailment need not remain false. Sorted solver declarations add an explicit
environment-domain condition. They do not change these logical obligations.
-/
namespace MicroCFTA.SourceEntailment
open FullSyntax SourceFormula

/-- A scoped formula query ranges over the environments admitted by its declarations. -/
def Entails (model : Interpretation Value) (admitted : (Name → Value) → Prop)
    (antecedent consequent : Formula) : Prop :=
  ∀ env, admitted env → Holds model env antecedent → Holds model env consequent

/-- Rename or identify names in a positive query. Source sort domains must be retained. -/
theorem rename_yes (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value)
    (source target : (Name → Value) → Prop) (renamed : List (Name × Name))
    (antecedent consequent : Formula)
    (domains : ∀ env, target env → source (renamedEnvironment model env renamed))
    (proved : Entails model source antecedent consequent) :
    Entails model target (substitute renamed antecedent) (substitute renamed consequent) := by
  intro env allowed assumed
  apply (substitute_semantics model nullary env renamed consequent).mpr
  exact proved _ (domains env allowed)
    ((substitute_semantics model nullary env renamed antecedent).mp assumed)

/-- Unrestricted positive entailment survives every simultaneous name identification. -/
theorem identify_yes (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (renamed : List (Name × Name))
    (antecedent consequent : Formula)
    (proved : Entails model (fun _ => True) antecedent consequent) :
    Entails model (fun _ => True) (substitute renamed antecedent) (substitute renamed consequent) :=
  rename_yes model nullary _ _ renamed antecedent consequent (fun _ _ => True.intro) proved

/-- Refutation can be transported when every relevant original environment can be lifted. -/
theorem rename_iff (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value)
    (source target : (Name → Value) → Prop) (renamed : List (Name × Name))
    (antecedent consequent : Formula)
    (domains : ∀ env, target env → source (renamedEnvironment model env renamed))
    (lifts : ∀ original, source original → ∃ env, target env ∧
      FormulaSemantics.Agree (formulaNames antecedent ++ formulaNames consequent)
        (renamedEnvironment model env renamed) original) :
    Entails model target (substitute renamed antecedent) (substitute renamed consequent) ↔
      Entails model source antecedent consequent := by
  constructor
  · intro proved original allowed assumed
    obtain ⟨env, targetAllowed, agree⟩ := lifts original allowed
    have left := FormulaSemantics.formula_ext model antecedent _ _
      (fun name member => agree name (List.mem_append_left _ member))
    have right := FormulaSemantics.formula_ext model consequent _ _
      (fun name member => agree name (List.mem_append_right _ member))
    apply right.mp
    apply (substitute_semantics model nullary env renamed consequent).mp
    apply proved env targetAllowed
    exact (substitute_semantics model nullary env renamed antecedent).mpr (left.mpr assumed)
  · exact rename_yes model nullary source target renamed antecedent consequent domains

/-- Extra actual assumptions only restrict the antecedent of a proved query. -/
theorem actual_assumptions_yes (model : Interpretation Value)
    (laws : FormulaSimplify.RelationLaws model) (admitted : (Name → Value) → Prop)
    (scopes : List (List (SourceGuards.Resolved Formula))) (antecedent consequent : Formula)
    (proved : Entails model admitted antecedent consequent) :
    Entails model admitted (SourceGuards.withActualAssumptions operations scopes antecedent) consequent := by
  intro env allowed assumed
  exact proved env allowed ((actual_assumptions_semantics model laws env scopes antecedent).mp assumed).2

/-- Solver soundness is a per-query contract over the actual declared environments. -/
def Sound (model : Interpretation Value)
    (admitted : List (Name × Name) → (Name → Value) → Prop)
    (solver : SourceGuards.Entailment Formula) : Prop :=
  ∀ bindings antecedent consequent,
    Guards.Supports (solver bindings antecedent consequent)
      (Entails model (admitted bindings) antecedent consequent)

/-- The source's unknown-identity safeguard preserves the sound per-query verdict. -/
theorem decideWith_sound (model : Interpretation Value)
    (admitted : List (Name × Name) → (Name → Value) → Prop)
    (solver : SourceGuards.Entailment Formula) (sound : Sound model admitted solver)
    (bindings : List (Name × Name)) (scopes : List (List (SourceGuards.Resolved Formula)))
    (antecedent consequent : Formula) :
    Guards.Supports (SourceGuards.decideWith solver bindings scopes antecedent consequent)
      (Entails model (admitted (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups)
        antecedent consequent) := by
  have certified := sound (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
    antecedent consequent
  cases result : solver (bindings ++ scopes.flatten.filterMap SourceGuards.Resolved.declaration).eraseDups
      antecedent consequent with
  | yes => simpa only [SourceGuards.decideWith, result, Guards.Supports] using certified
  | unknown => simp only [SourceGuards.decideWith, result, Guards.Supports]
  | no =>
      by_cases known : scopes.all (fun scope => scope.all SourceGuards.Resolved.identityKnown) = true
      · simpa only [SourceGuards.decideWith, result, known, ↓reduceIte, Guards.Supports] using certified
      · simp only [SourceGuards.decideWith, result, known, Bool.false_eq_true, ↓reduceIte, Guards.Supports]

/-- Two independent names are not provably equal over the integers. -/
theorem distinct_names_not_entailed :
    ¬Entails integerModel (fun _ => True) .top (.atom .eq (.var "left") (.var "right")) := by
  intro proved
  have impossible := proved (fun name => if name = "left" then 0 else 1) True.intro (by simp [Holds])
  simp [Holds, evaluateTerm, integerModel, CoreFormula.evalRelation] at impossible

/-- Identifying both names makes that failed entailment valid. Refutations cannot be copied blindly. -/
theorem identification_changes_no_to_yes :
    Entails integerModel (fun _ => True)
      (substitute [("left", "actual"), ("right", "actual")] .top)
      (substitute [("left", "actual"), ("right", "actual")] (.atom .eq (.var "left") (.var "right"))) := by
  intro env _ _
  have calculated : substitute [("left", "actual"), ("right", "actual")]
      (.atom .eq (.var "left") (.var "right")) = .atom .eq (.var "actual") (.var "actual") := by
    decide +kernel
  rw [calculated]
  simp [Holds, evaluateTerm, integerModel, CoreFormula.evalRelation]

end MicroCFTA.SourceEntailment
