import MicroCFTA.SourceActuals
import MicroCFTA.FormulaCorrectness
import MicroCFTA.FormulaExecutable

/-!
# Formula operations used by the guard evaluator

Every evaluator substitution replaces a name by a name. The checked formula
substitution cannot reject this input, including below function applications
and quantifiers. The total wrapper executes that checked implementation.
-/
namespace MicroCFTA.SourceFormula
open FullSyntax FormulaSubstitution

attribute [local simp] LatticeLinear.except_map_ok LatticeLinear.except_bind_ok

private theorem pure_ok (value : α) : (pure value : Except Error α) = .ok value := rfl
attribute [local simp] pure_ok

/-- Every active replacement is a named variable. -/
def NameOnly (active : List (Name × Term)) : Prop :=
  ∀ entry ∈ active, ∃ name, entry.2 = .var name

theorem nameOnly_filter (active : List (Name × Term)) (keep : (Name × Term) → Bool)
    (names : NameOnly active) : NameOnly (active.filter keep) := by
  intro entry member
  exact names entry (List.mem_filter.mp member).1

/-- Capture avoidance introduces only named-variable replacements. -/
theorem prepare_nameOnly (active : List (Name × Term)) (bound : List (Name × ValueSort))
    (bodyNames : List Name) (names : NameOnly active) :
    NameOnly (prepare active bound bodyNames).2 := by
  intro entry member
  simp only [prepare, List.mem_append, List.mem_map] at member
  rcases member with ⟨pair, _, rfl⟩ | kept
  · exact ⟨pair.2, rfl⟩
  · exact names entry (List.mem_filter.mp kept).1

mutual
/-- Name-only term substitution succeeds for every current term constructor. -/
theorem term_total (active : List (Name × Term)) (names : NameOnly active) (input : Term) :
    ∃ output, term active input = .ok output := by
  cases input with
  | lit n | var n => simp [term]
  | app name args =>
      cases args with
      | nil => simp [term]
      | cons argument rest =>
          obtain ⟨out, success⟩ := arguments_total active names (argument :: rest)
          cases found : lookup name active with
          | none => simp [term, found, success]
          | some replacement =>
              obtain ⟨renamed, same⟩ := names (name, replacement) (lookup_member active name replacement found)
              simp only at same
              subst replacement
              simp [term, found, success]
  | neg t => obtain ⟨out, success⟩ := term_total active names t; simp [term, success]
  | cast t sort => obtain ⟨out, success⟩ := term_total active names t; simp [term, success]
  | add t u | sub t u | mul t u | div t u | mod t u =>
      obtain ⟨left, hl⟩ := term_total active names t
      obtain ⟨right, hr⟩ := term_total active names u
      simp [term, hl, hr, Bind.bind, Except.bind]
  | ite p t u =>
      obtain ⟨condition, hp⟩ := formula_total active names p
      obtain ⟨left, hl⟩ := term_total active names t
      obtain ⟨right, hr⟩ := term_total active names u
      simp [term, hp, hl, hr, Bind.bind, Except.bind]
termination_by sizeOf input

/-- Name-only argument traversal retains every argument. -/
theorem arguments_total (active : List (Name × Term)) (names : NameOnly active) (input : List Term) :
    ∃ output, arguments active input = .ok output := by
  cases input with
  | nil => simp [arguments]
  | cons t ts =>
      obtain ⟨head, hh⟩ := term_total active names t
      obtain ⟨tail, ht⟩ := arguments_total active names ts
      simp [arguments, hh, ht, Bind.bind, Except.bind]
termination_by sizeOf input

/-- Name-only formula substitution succeeds below both quantifier kinds. -/
theorem formula_total (active : List (Name × Term)) (names : NameOnly active) (input : Formula) :
    ∃ output, formula active input = .ok output := by
  cases input with
  | top | bottom => simp [formula]
  | and ps | or ps =>
      obtain ⟨out, success⟩ := parts_total active names ps
      simp [formula, success]
  | not p =>
      obtain ⟨out, success⟩ := formula_total active names p
      simp [formula, success]
  | atom relation t u =>
      obtain ⟨left, hl⟩ := term_total active names t
      obtain ⟨right, hr⟩ := term_total active names u
      simp [formula, hl, hr, Bind.bind, Except.bind]
  | «forall» bound p | «exists» bound p =>
      obtain ⟨out, success⟩ := formula_total _ (prepare_nameOnly active bound (formulaNames p) names) p
      simp [formula, success]
termination_by sizeOf input

/-- Name-only Boolean traversal retains every formula part. -/
theorem parts_total (active : List (Name × Term)) (names : NameOnly active) (input : List Formula) :
    ∃ output, parts active input = .ok output := by
  cases input with
  | nil => simp [parts]
  | cons p ps =>
      obtain ⟨head, hh⟩ := formula_total active names p
      obtain ⟨tail, ht⟩ := parts_total active names ps
      simp [parts, hh, ht, Bind.bind, Except.bind]
termination_by sizeOf input
end

/-- Convert the guard's name pairs to the public formula replacement syntax. -/
def replacements (renamed : List (Name × Name)) : List (Name × Term) :=
  renamed.map (fun entry => (entry.1, .var entry.2))

theorem replacements_nameOnly (renamed : List (Name × Name)) : NameOnly (replacements renamed) := by
  intro entry member
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp member
  exact ⟨pair.2, rfl⟩

/-- The checked public substitution never errors on a guard-generated replacement list. -/
theorem checked_total (renamed : List (Name × Name)) (input : Formula) :
    ∃ output, checked (replacements renamed) input = .ok output :=
  formula_total _ (nameOnly_filter _ _ (replacements_nameOnly renamed)) input

/-- Execute the checked implementation. Its error arm is unreachable for name pairs. -/
def substitute (renamed : List (Name × Name)) (input : Formula) : Formula :=
  match checked (replacements renamed) input with
  | .ok output => output
  | .error _ => input

/-- The total wrapper returns exactly the public checked result. -/
theorem substitute_checked (renamed : List (Name × Name)) (input : Formula) :
    checked (replacements renamed) input = .ok (substitute renamed input) := by
  obtain ⟨output, success⟩ := checked_total renamed input
  simp [substitute, success]

/-- Guard name replacement has the full capture-avoiding formula meaning. -/
theorem substitute_semantics (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (env : Name → Value)
    (renamed : List (Name × Name)) (input : Formula) :
    Holds model env (substitute renamed input) ↔ Holds model
      (assignment model env ((replacements renamed).filter fun entry => !identityReplacement entry)) input :=
  FormulaCorrectness.checked_semantics model nullary _ _ _ (substitute_checked renamed input) env

/-- Instantiate every formula operation of the full source guard evaluator. -/
def operations : SourceGuards.Formulas Formula where
  substitute := substitute
  negate := Formula.not
  conjunction := fun parts => FormulaExecutable.simplify (.and parts)
  equalNames := fun left right => .atom .eq (.var left) (.var right)
  freeNames := freeNames

/-- The source conjunction requires every supplied assumption. -/
theorem conjunction_semantics (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (env : Name → Value) (parts : List Formula) :
    Holds model env (operations.conjunction parts) ↔ ∀ part ∈ parts, Holds model env part := by
  exact (FormulaExecutable.simplify_semantics model laws env (.and parts)).trans
    (by simpa [Holds] using FormulaSimplify.all_iff model env parts)

/-- Source formula negation negates truth under the same ambient environment. -/
theorem negate_semantics (model : Interpretation Value) (env : Name → Value) (input : Formula) :
    Holds model env (operations.negate input) ↔ ¬Holds model env input := by simp [operations, Holds]

/-- Contract aliases refer to the two ambient values through the equality relation. -/
theorem alias_semantics (model : Interpretation Value) (env : Name → Value) (left right : Name) :
    Holds model env (operations.equalNames left right) ↔ model.relation .eq (env left) (env right) := by
  simp [operations, Holds, evaluateTerm]

/-- An ambient name environment after the checked simultaneous replacement policy. -/
noncomputable def renamedEnvironment (model : Interpretation Value) (env : Name → Value)
    (renamed : List (Name × Name)) : Name → Value :=
  assignment model env ((replacements renamed).filter fun entry => !identityReplacement entry)

/-- Nested scopes act on environments in the reverse order of formula construction. -/
noncomputable def scopeEnvironment (model : Interpretation Value) (env : Name → Value)
    (scopes : List (List (SourceGuards.Resolved Formula))) : Name → Value :=
  scopes.foldr (fun scope nested => renamedEnvironment model nested (scope.map SourceGuards.Resolved.replacement)) env

/-- The full scope fold has the capture-avoiding formula meaning, with no opaque substitution premise. -/
theorem scopes_semantics (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value) (env : Name → Value)
    (scopes : List (List (SourceGuards.Resolved Formula))) (input : Formula) :
    Holds model env (SourceGuards.applySubstitutions operations scopes input) ↔
      Holds model (scopeEnvironment model env scopes) input := by
  induction scopes generalizing input with
  | nil => rfl
  | cons first rest ih =>
      change Holds model env (SourceGuards.applySubstitutions operations rest
        (substitute (first.map SourceGuards.Resolved.replacement) input)) ↔ _
      rw [ih]
      exact substitute_semantics model nullary _ _ input

/-- Actual assumptions keep their ambient meaning outside the nested scope fold. -/
theorem actual_assumptions_semantics (model : Interpretation Value)
    (laws : FormulaSimplify.RelationLaws model) (env : Name → Value)
    (scopes : List (List (SourceGuards.Resolved Formula))) (input : Formula) :
    Holds model env (SourceGuards.withActualAssumptions operations scopes input) ↔
      (∀ scope ∈ scopes, ∀ resolved ∈ scope, Holds model env resolved.actualAssumption) ∧
      Holds model env input := by
  rw [SourceGuards.withActualAssumptions, conjunction_semantics model laws]
  simp only [List.mem_append, List.mem_map, List.mem_flatten, List.mem_singleton]
  constructor
  · intro all
    exact ⟨fun scope hs resolved hr => all _ (Or.inl ⟨resolved, ⟨scope, hs, hr⟩, rfl⟩),
      all input (Or.inr rfl)⟩
  · rintro ⟨all, body⟩ part (⟨resolved, ⟨scope, hs, hr⟩, rfl⟩ | rfl)
    · exact all scope hs resolved hr
    · exact body

/-- Concrete public complete-term evaluation uses the repaired full formula backend. -/
def evaluateGuard (solver : SourceGuards.Entailment Formula) (guard : SourceGuards.Guard Formula)
    (term : Language.Term (SourceObservations.Label Formula)) : Guards.Verdict :=
  SourceObservations.evaluateGuard operations solver guard term

/-- Concrete public sparse evaluation uses the same repaired backend. -/
def evaluateGuardWithShape (solver : SourceGuards.Entailment Formula)
    (observed : SourceGuards.Observations Formula) (guard : SourceGuards.Guard Formula) : Guards.Verdict :=
  SourceObservations.evaluateGuardWithShape operations solver observed guard

end MicroCFTA.SourceFormula
