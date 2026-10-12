import MicroCFTA.SourceActualAssumptions

/-!
# Nested scope environments commute with source fresh-name maps

The proof retains duplicate formal names and the source identity filter. Its
finite invariants are closure of scope names, fixed formal names, and
injectivity of the actual fresh-name map on the relevant names.
-/
namespace MicroCFTA.SourceScopeEnvironment
open FullSyntax FormulaSubstitution SourceFormula FreshEnvironment

/-- The exact environment effect of one checked name-pair entry, including identity removal. -/
theorem environment_cons (model : Interpretation Value) (env : Name → Value)
    (formal actual name : Name) (rest : List (Name × Name)) :
    renamedEnvironment model env ((formal, actual) :: rest) name =
      if formal = actual then renamedEnvironment model env rest name else
      if name = formal then env actual else renamedEnvironment model env rest name := by
  by_cases identity : formal = actual <;> by_cases same : name = formal <;>
    simp [renamedEnvironment, replacements, identityReplacement, assignment, FullSyntax.lookup,
      identity, same, evaluateTerm]

/-- Apply a fresh spelling map to logical values while keeping literal formal names. -/
def scopeNames (renamed : List (Name × Name)) (entries : List (Name × Name)) : List (Name × Name) :=
  entries.map (fun entry => (entry.1, renameName renamed entry.2))

/-- Two environments agree on the relevant names through the chosen name map. -/
def Related (renamed : List (Name × Name)) (live : List Name) (first second : Name → Value) : Prop :=
  ∀ name ∈ live, first name = second (renameName renamed name)

/-- Unique targets and avoidance of unmapped live names make the finite spelling map injective on live names. -/
theorem injective_live (renamed : List (Name × Name)) (live : List Name)
    (unique : (renamed.map Prod.snd).Nodup)
    (avoid : ∀ name ∈ live, name ∉ renamed.map Prod.fst → name ∉ renamed.map Prod.snd)
    (left : Name) (leftLive : left ∈ live) (right : Name) (rightLive : right ∈ live)
    (same : renameName renamed left = renameName renamed right) : left = right := by
  by_cases leftKey : left ∈ renamed.map Prod.fst
  · have first := FormulaBinders.rename_member renamed left leftKey
    by_cases rightKey : right ∈ renamed.map Prod.fst
    · have second := FormulaBinders.rename_member renamed right rightKey
      rw [same] at first
      exact FormulaBinders.target_injective renamed unique left right _ first second
    · have fixed := FormulaBinders.rename_absent renamed right rightKey
      have mapped : renameName renamed left = right := same.trans fixed
      have target : right ∈ renamed.map Prod.snd := List.mem_map.mpr ⟨_, first, mapped⟩
      exact False.elim (avoid right rightLive rightKey target)
  · have fixed := FormulaBinders.rename_absent renamed left leftKey
    by_cases rightKey : right ∈ renamed.map Prod.fst
    · have second := FormulaBinders.rename_member renamed right rightKey
      have mapped : renameName renamed right = left := same.symm.trans fixed
      have target : left ∈ renamed.map Prod.snd := List.mem_map.mpr ⟨_, second, mapped⟩
      exact False.elim (avoid left leftLive leftKey target)
    · simpa [fixed, FormulaBinders.rename_absent renamed right rightKey] using same

/-- The reverse table from FreshEnvironment constructs the initial finite environment relation. -/
theorem lift_related (model : Interpretation Value) (renamed : List (Name × Name)) (live : List Name)
    (keys : (renamed.map Prod.fst).Nodup) (targets : (renamed.map Prod.snd).Nodup)
    (avoid : ∀ name ∈ live, name ∉ renamed.map Prod.fst → name ∉ renamed.map Prod.snd)
    (original : Name → Value) : Related renamed live original (liftEnvironment renamed original) := by
  intro name member
  have lifted := lift_agree model renamed live keys targets avoid original name member
  rw [environment_names model _ renamed keys name] at lifted
  exact lifted.symm

/-- One simultaneous scope preserves the finite environment relation, even with repeated formal names. -/
theorem environment_commutes (model : Interpretation Value) (renamed : List (Name × Name)) (live : List Name)
    (injective : ∀ left ∈ live, ∀ right ∈ live, renameName renamed left = renameName renamed right → left = right)
    (first second : Name → Value) (related : Related renamed live first second)
    (entries : List (Name × Name))
    (closed : ∀ entry ∈ entries, entry.1 ∈ live ∧ entry.2 ∈ live ∧ renameName renamed entry.1 = entry.1) :
    Related renamed live (renamedEnvironment model first entries)
      (renamedEnvironment model second (scopeNames renamed entries)) := by
  intro name member
  induction entries with
  | nil => exact related name member
  | cons entry rest ih =>
      rcases entry with ⟨formal, actual⟩
      have declared := closed (formal, actual) (by simp)
      have tail := ih (fun value present => closed value (by simp [present]))
      simp only [scopeNames, List.map_cons, environment_cons]
      by_cases identity : formal = actual
      · subst actual
        simp only [declared.2.2, ↓reduceIte]
        exact tail
      · have renamedDifferent : formal ≠ renameName renamed actual := by
          intro equal
          exact identity (injective formal declared.1 actual declared.2.1 (declared.2.2.trans equal))
        simp only [identity, renamedDifferent, ↓reduceIte]
        by_cases matching : name = formal
        · subst name
          simpa only [declared.2.2, ↓reduceIte] using related actual declared.2.1
        · have mappedDifferent : renameName renamed name ≠ formal := by
            intro equal
            exact matching (injective name member formal declared.1 (equal.trans declared.2.2.symm))
          simp only [matching, mappedDifferent, ↓reduceIte]
          exact tail

/-- Ordered source resolved records induce the exact logical name-pair map. -/
theorem aligned_replacements (renamed : List (Name × Name))
    (first second : List (SourceGuards.Resolved Formula))
    (aligned : Language.All₂ (SourceResolvedTables.Aligned renamed) first second) :
    second.map SourceGuards.Resolved.replacement = scopeNames renamed (first.map SourceGuards.Resolved.replacement) := by
  induction aligned with
  | nil => rfl
  | cons head tail ih => simp [scopeNames, head.1, ih]

/-- The complete reverse-order environment fold preserves the same finite relation. -/
theorem scopes_commute (model : Interpretation Value) (renamed : List (Name × Name)) (live : List Name)
    (injective : ∀ left ∈ live, ∀ right ∈ live, renameName renamed left = renameName renamed right → left = right)
    (firstEnv secondEnv : Name → Value) (related : Related renamed live firstEnv secondEnv)
    (first second : List (List (SourceGuards.Resolved Formula)))
    (aligned : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second)
    (closed : ∀ scope ∈ first, ∀ entry ∈ scope,
      entry.replacement.1 ∈ live ∧ entry.replacement.2 ∈ live ∧ renameName renamed entry.replacement.1 = entry.replacement.1) :
    Related renamed live (scopeEnvironment model firstEnv first) (scopeEnvironment model secondEnv second) := by
  induction aligned with
  | nil => exact related
  | @cons firstScope secondScope firstRest secondRest head tail ih =>
      have tailRelated := ih (fun scope member => closed scope (List.mem_cons_of_mem _ member))
      simp only [scopeEnvironment, List.foldr_cons]
      rw [aligned_replacements renamed firstScope secondScope head]
      apply environment_commutes model renamed live injective _ _ tailRelated
      intro entry member
      obtain ⟨resolved, present, rfl⟩ := List.mem_map.mp member
      exact closed firstScope (by simp) resolved present

/-- Nested source scope formulas agree when original free names are fixed and the finite scope invariant holds. -/
theorem scoped_formula_equivalent (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (renamed : List (Name × Name)) (live : List Name)
    (injective : ∀ left ∈ live, ∀ right ∈ live, renameName renamed left = renameName renamed right → left = right)
    (firstEnv secondEnv : Name → Value) (related : Related renamed live firstEnv secondEnv)
    (first second : List (List (SourceGuards.Resolved Formula)))
    (aligned : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second)
    (closed : ∀ scope ∈ first, ∀ entry ∈ scope,
      entry.replacement.1 ∈ live ∧ entry.replacement.2 ∈ live ∧ renameName renamed entry.replacement.1 = entry.replacement.1)
    (formula : Formula) (names : ∀ name ∈ formulaNames formula, name ∈ live ∧ renameName renamed name = name) :
    Holds model firstEnv (SourceGuards.applySubstitutions operations first formula) ↔
      Holds model secondEnv (SourceGuards.applySubstitutions operations second formula) := by
  rw [scopes_semantics model nullary, scopes_semantics model nullary]
  apply FormulaSemantics.formula_ext
  intro name member
  obtain ⟨liveName, fixed⟩ := names name member
  have exact := scopes_commute model renamed live injective firstEnv secondEnv related first second aligned closed name liveName
  simpa only [fixed] using exact

end MicroCFTA.SourceScopeEnvironment
