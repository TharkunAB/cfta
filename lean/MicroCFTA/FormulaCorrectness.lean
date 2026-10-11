import MicroCFTA.FormulaBinders

/-!
# Complete checked substitution correctness

The theorem covers every sorted formula constructor and every capture-renaming
case. Primitive arithmetic, function values, casts, and sort domains are
parameters. Nullary application denotes its named value, as the source's
Liquid Fixpoint lowering does. Unsupported non-name function replacements
remain explicit failures.
-/

namespace MicroCFTA.FormulaCorrectness

open FullSyntax FormulaSubstitution

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error
  LatticeLinear.except_map_ok LatticeLinear.except_map_error

mutual
/-- Successful checked term substitution preserves arbitrary primitive semantics. -/
theorem term_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (active : List (Name × Term)) (input output : Term)
    (success : term active input = .ok output) (env : Name → Value) :
    evaluateTerm model env output = evaluateTerm model (assignment model env active) input := by
  cases input with
  | lit n => simp [term] at success; subst output; simp [evaluateTerm]
  | var name =>
      cases found : lookup name active <;> simp [term, found] at success <;>
        subst output <;> simp [assignment, evaluateTerm, found]
  | app name args =>
      cases args with
      | nil =>
          cases found : lookup name active <;> simp [term, found] at success <;>
            subst output <;> simp [assignment, evaluateTerm, evaluateTerms, found, nullary]
      | cons arg args =>
          cases found : lookup name active with
          | none =>
              cases done : arguments active (arg :: args) with
              | error error => simp [term, found, done] at success
              | ok replaced =>
                  simp [term, found, done] at success
                  subst output
                  simp only [evaluateTerm]
                  rw [arguments_semantics model nullary active _ replaced done env]
                  simp [assignment, found]
          | some replacement =>
              cases replacement with
              | var renamed =>
                  cases done : arguments active (arg :: args) with
                  | error error => simp [term, found, done] at success
                  | ok replaced =>
                      simp [term, found, done] at success
                      subst output
                      simp only [evaluateTerm]
                      rw [arguments_semantics model nullary active _ replaced done env]
                      simp [assignment, found, evaluateTerm]
              | _ => simp [term, found] at success
  | neg t | cast t sort =>
      cases done : term active t with
      | error error => simp [term, done] at success
      | ok replaced =>
          simp [term, done] at success
          subst output
          simp only [evaluateTerm]
          rw [term_semantics model nullary active t replaced done env]
  | add t u | sub t u | mul t u | div t u | mod t u =>

      cases dt : term active t with
      | error error => simp [term, dt] at success
      | ok rt =>
          cases du : term active u with
          | error error => simp [term, dt, du] at success
          | ok ru =>
              simp [term, dt, du] at success
              subst output
              simp only [evaluateTerm]
              rw [term_semantics model nullary active t rt dt env,
                term_semantics model nullary active u ru du env]
  | ite p t u =>

      cases dp : formula active p with
      | error error => simp [term, dp] at success
      | ok rp =>
          cases dt : term active t with
          | error error => simp [term, dp, dt] at success
          | ok rt =>
              cases du : term active u with
              | error error => simp [term, dp, dt, du] at success
              | ok ru =>
                  simp [term, dp, dt, du] at success
                  subst output
                  have hp := formula_semantics model nullary active p rp dp env
                  have ht := term_semantics model nullary active t rt dt env
                  have hu := term_semantics model nullary active u ru du env
                  simp only [evaluateTerm, ht, hu]
                  by_cases holds : Holds model env rp
                  · simp [holds, hp.mp holds]
                  · have no : ¬Holds model (assignment model env active) p := fun yes => holds (hp.mpr yes)
                    simp [holds, no]
termination_by sizeOf input

/-- Successful checked argument substitution preserves order and every interpreted argument. -/
theorem arguments_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (active : List (Name × Term)) (input output : List Term)
    (success : arguments active input = .ok output) (env : Name → Value) :
    evaluateTerms model env output = evaluateTerms model (assignment model env active) input := by
  cases input with
  | nil => simp [arguments] at success; subst output; simp [evaluateTerms]
  | cons t ts =>

      cases dt : term active t with
      | error error => simp [arguments, dt] at success
      | ok rt =>
          cases ds : arguments active ts with
          | error error => simp [arguments, dt, ds] at success
          | ok rs =>
              simp [arguments, dt, ds] at success
              subst output
              simp only [evaluateTerms]
              rw [term_semantics model nullary active t rt dt env,
                arguments_semantics model nullary active ts rs ds env]
termination_by sizeOf input

/-- Checked substitution is semantically exact for every constructor. -/
theorem formula_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (active : List (Name × Term)) (input output : Formula)
    (success : formula active input = .ok output) (env : Name → Value) :
    Holds model env output ↔ Holds model (assignment model env active) input := by
  cases input with
  | top | bottom => simp [formula] at success; subst output; simp [Holds]
  | and ps | or ps =>
      cases done : parts active ps with
      | error error => simp [formula, done] at success
      | ok replaced =>
          simp [formula, done] at success
          subst output
          have both := parts_semantics model nullary active ps replaced done env
          simp only [Holds]
          first | exact both.1 | exact both.2
  | not p =>
      cases done : formula active p with
      | error error => simp [formula, done] at success
      | ok replaced =>
          simp [formula, done] at success
          subst output
          simpa only [Holds] using not_congr (formula_semantics model nullary active p replaced done env)
  | atom relation t u =>

      cases dt : term active t with
      | error error => simp [formula, dt] at success
      | ok rt =>
          cases du : term active u with
          | error error => simp [formula, dt, du] at success
          | ok ru =>
              simp [formula, dt, du] at success
              subst output
              simp only [Holds]
              rw [term_semantics model nullary active t rt dt env,
                term_semantics model nullary active u ru du env]
  | «forall» bound p | «exists» bound p =>
      cases prepared : prepare active bound (formulaNames p) with
      | mk newBound newActive =>
          cases done : formula newActive p with
          | error error => simp [formula, prepared, done] at success
          | ok replaced =>
              simp [formula, prepared, done] at success
              subst output
              have body : ∀ assigned, Holds model assigned replaced ↔
                  Holds model (assignment model assigned (prepare active bound (formulaNames p)).2) p := by
                intro assigned
                simpa [prepared] using formula_semantics model nullary newActive p replaced done assigned
              first
              | simpa [prepared] using FormulaBinders.prepared_all model env active bound p replaced body
              | simpa [prepared] using FormulaBinders.prepared_exists model env active bound p replaced body

termination_by sizeOf input

/-- Checked substitution preserves conjunction and disjunction list semantics. -/
theorem parts_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (active : List (Name × Term)) (input output : List Formula)
    (success : parts active input = .ok output) (env : Name → Value) :
    (holdsAll model env output ↔ holdsAll model (assignment model env active) input) ∧
      (holdsAny model env output ↔ holdsAny model (assignment model env active) input) := by
  cases input with
  | nil => simp [parts] at success; subst output; simp [holdsAll, holdsAny]
  | cons p ps =>

      cases dp : formula active p with
      | error error => simp [parts, dp] at success
      | ok rp =>
          cases ds : parts active ps with
          | error error => simp [parts, dp, ds] at success
          | ok rs =>
              simp [parts, dp, ds] at success
              subst output
              have hp := formula_semantics model nullary active p rp dp env
              have hs := parts_semantics model nullary active ps rs ds env
              simp only [holdsAll, holdsAny, hp, hs.1, hs.2, iff_self, and_self]
termination_by sizeOf input
end

/-- The public checked API preserves the source's identity filtering and simultaneous replacement meaning. -/
theorem checked_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (replacements : List (Name × Term)) (input output : Formula)
    (success : checked replacements input = .ok output) (env : Name → Value) :
    Holds model env output ↔ Holds model
      (assignment model env (replacements.filter fun entry => !identityReplacement entry)) input := by
  exact formula_semantics model nullary _ input output success env

/-- A substitution whose keys are absent cannot change the formula's meaning, even if it renames binders. -/
theorem checked_absent (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (replacements : List (Name × Term)) (input output : Formula)
    (absent : ∀ entry ∈ replacements, entry.1 ∉ formulaNames input)
    (success : checked replacements input = .ok output) (env : Name → Value) :
    Holds model env output ↔ Holds model env input := by
  apply Iff.trans (checked_semantics model nullary replacements input output success env)
  apply FormulaSemantics.formula_ext
  intro name member
  cases found : lookup name (replacements.filter fun entry => !identityReplacement entry) with
  | none => simp [assignment, found]
  | some replacement =>
      have present := lookup_member _ name replacement found
      exact False.elim (absent (name, replacement) (List.mem_filter.mp present).1 member)

end MicroCFTA.FormulaCorrectness
