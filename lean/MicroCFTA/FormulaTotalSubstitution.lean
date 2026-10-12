import MicroCFTA.SourceFormula

/-!
# The total public substitution policy

At `092b56d`, the total API retains an unsupported application head and
substitutes its arguments. The checked API reports the first failure after
it visits those arguments. Both APIs have the same result on checked success.
The total fallback does not implement arbitrary function-value replacement.
-/
namespace MicroCFTA.FormulaTotalSubstitution
open FullSyntax

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error
  LatticeLinear.except_map_ok LatticeLinear.except_map_error

mutual
/-- Substitute terms and retain an unsupported named application head. -/
def term (active : List (Name × Term)) : Term → Term
  | .lit n => .lit n
  | .var name => (lookup name active).getD (.var name)
  | .app name [] => (lookup name active).getD (.app name [])
  | .app name (argument :: rest) =>
      let head := match lookup name active with | some (.var renamed) => renamed | _ => name
      .app head (arguments active (argument :: rest))
  | .neg t => .neg (term active t)
  | .add t u => .add (term active t) (term active u)
  | .sub t u => .sub (term active t) (term active u)
  | .mul t u => .mul (term active t) (term active u)
  | .div t u => .div (term active t) (term active u)
  | .mod t u => .mod (term active t) (term active u)
  | .ite p t u => .ite (formula active p) (term active t) (term active u)
  | .cast t sort => .cast (term active t) sort
termination_by t => sizeOf t

/-- Visit every argument in source order. -/
def arguments (active : List (Name × Term)) : List Term → List Term
  | [] => []
  | t :: ts => term active t :: arguments active ts
termination_by ts => sizeOf ts

/-- Retain all formula constructors and use the source binder preparation. -/
def formula (active : List (Name × Term)) : Formula → Formula
  | .top => .top
  | .bottom => .bottom
  | .and ps => .and (parts active ps)
  | .or ps => .or (parts active ps)
  | .not p => .not (formula active p)
  | .atom r t u => .atom r (term active t) (term active u)
  | .forall bound p =>
      let (renamed, nested) := FormulaSubstitution.prepare active bound (formulaNames p)
      .forall renamed (formula nested p)
  | .exists bound p =>
      let (renamed, nested) := FormulaSubstitution.prepare active bound (formulaNames p)
      .exists renamed (formula nested p)
termination_by p => sizeOf p

/-- Visit every Boolean part in source order. -/
def parts (active : List (Name × Term)) : List Formula → List Formula
  | [] => []
  | p :: ps => formula active p :: parts active ps
termination_by ps => sizeOf ps
end

/-- Remove identity entries once at the public API boundary. -/
def substitute (replacements : List (Name × Term)) (input : Formula) : Formula :=
  formula (replacements.filter fun entry => !identityReplacement entry) input

mutual
/-- Checked term success agrees with the total source traversal. -/
theorem term_checked (active : List (Name × Term)) (input output : Term)
    (success : FormulaSubstitution.term active input = .ok output) : term active input = output := by
  cases input with
  | lit n | var n => simpa [FormulaSubstitution.term, term] using success
  | app name args =>
      cases args with
      | nil => simpa [FormulaSubstitution.term, term] using success
      | cons arg args =>
          cases found : lookup name active with
          | none =>
              cases done : FormulaSubstitution.arguments active (arg :: args) with
              | error error => simp [FormulaSubstitution.term, found, done] at success
              | ok replaced =>
                  simp [FormulaSubstitution.term, found, done] at success
                  subst output
                  simp only [term, found]
                  rw [arguments_checked active _ _ done]
          | some replacement =>
              cases replacement with
              | var renamed =>
                  cases done : FormulaSubstitution.arguments active (arg :: args) with
                  | error error => simp [FormulaSubstitution.term, found, done] at success
                  | ok replaced =>
                      simp [FormulaSubstitution.term, found, done] at success
                      subst output
                      simp only [term, found]
                      rw [arguments_checked active _ _ done]
              | _ => cases done : FormulaSubstitution.arguments active (arg :: args) <;>
                  simp [FormulaSubstitution.term, found, done] at success
  | neg t | cast t sort =>
      cases done : FormulaSubstitution.term active t with
      | error error => simp [FormulaSubstitution.term, done] at success
      | ok replaced =>
          simp [FormulaSubstitution.term, done] at success
          subst output
          simp only [term, term_checked active _ _ done]
  | add t u | sub t u | mul t u | div t u | mod t u =>
      cases dt : FormulaSubstitution.term active t with
      | error error => simp [FormulaSubstitution.term, dt] at success
      | ok rt =>
          cases du : FormulaSubstitution.term active u with
          | error error => simp [FormulaSubstitution.term, dt, du] at success
          | ok ru =>
              simp [FormulaSubstitution.term, dt, du] at success
              subst output
              simp only [term, term_checked active _ _ dt, term_checked active _ _ du]
  | ite p t u =>
      cases dp : FormulaSubstitution.formula active p with
      | error error => simp [FormulaSubstitution.term, dp] at success
      | ok rp =>
          cases dt : FormulaSubstitution.term active t with
          | error error => simp [FormulaSubstitution.term, dp, dt] at success
          | ok rt =>
              cases du : FormulaSubstitution.term active u with
              | error error => simp [FormulaSubstitution.term, dp, dt, du] at success
              | ok ru =>
                  simp [FormulaSubstitution.term, dp, dt, du] at success
                  subst output
                  simp only [term, formula_checked active _ _ dp, term_checked active _ _ dt,
                    term_checked active _ _ du]
termination_by sizeOf input

/-- Checked argument success agrees at every position. -/
theorem arguments_checked (active : List (Name × Term)) (input output : List Term)
    (success : FormulaSubstitution.arguments active input = .ok output) : arguments active input = output := by
  cases input with
  | nil => simpa [FormulaSubstitution.arguments, arguments] using success
  | cons t ts =>
      cases dt : FormulaSubstitution.term active t with
      | error error => simp [FormulaSubstitution.arguments, dt] at success
      | ok rt =>
          cases ds : FormulaSubstitution.arguments active ts with
          | error error => simp [FormulaSubstitution.arguments, dt, ds] at success
          | ok rs =>
              simp [FormulaSubstitution.arguments, dt, ds] at success
              subst output
              simp only [arguments, term_checked active _ _ dt, arguments_checked active _ _ ds]
termination_by sizeOf input

/-- Checked formula success agrees under every connective and sorted binder. -/
theorem formula_checked (active : List (Name × Term)) (input output : Formula)
    (success : FormulaSubstitution.formula active input = .ok output) : formula active input = output := by
  cases input with
  | top | bottom => simpa [FormulaSubstitution.formula, formula] using success
  | and ps | or ps =>
      cases done : FormulaSubstitution.parts active ps with
      | error error => simp [FormulaSubstitution.formula, done] at success
      | ok replaced =>
          simp [FormulaSubstitution.formula, done] at success
          subst output
          simp only [formula, parts_checked active _ _ done]
  | not p =>
      cases done : FormulaSubstitution.formula active p with
      | error error => simp [FormulaSubstitution.formula, done] at success
      | ok replaced =>
          simp [FormulaSubstitution.formula, done] at success
          subst output
          simp only [formula, formula_checked active _ _ done]
  | atom r t u =>
      cases dt : FormulaSubstitution.term active t with
      | error error => simp [FormulaSubstitution.formula, dt] at success
      | ok rt =>
          cases du : FormulaSubstitution.term active u with
          | error error => simp [FormulaSubstitution.formula, dt, du] at success
          | ok ru =>
              simp [FormulaSubstitution.formula, dt, du] at success
              subst output
              simp only [formula, term_checked active _ _ dt, term_checked active _ _ du]
  | «forall» bound p | «exists» bound p =>
      cases done : FormulaSubstitution.formula (FormulaSubstitution.prepare active bound (formulaNames p)).2 p with
      | error error => simp [FormulaSubstitution.formula, done] at success
      | ok replaced =>
          simp [FormulaSubstitution.formula, done] at success
          subst output
          simp only [formula, formula_checked _ _ _ done]
termination_by sizeOf input

/-- Checked Boolean traversal success agrees at every position. -/
theorem parts_checked (active : List (Name × Term)) (input output : List Formula)
    (success : FormulaSubstitution.parts active input = .ok output) : parts active input = output := by
  cases input with
  | nil => simpa [FormulaSubstitution.parts, parts] using success
  | cons p ps =>
      cases dp : FormulaSubstitution.formula active p with
      | error error => simp [FormulaSubstitution.parts, dp] at success
      | ok rp =>
          cases ds : FormulaSubstitution.parts active ps with
          | error error => simp [FormulaSubstitution.parts, dp, ds] at success
          | ok rs =>
              simp [FormulaSubstitution.parts, dp, ds] at success
              subst output
              simp only [parts, formula_checked active _ _ dp, parts_checked active _ _ ds]
termination_by sizeOf input
end

/-- The two public APIs coincide on every successful checked result. -/
theorem checked_agrees (replacements : List (Name × Term)) (input output : Formula)
    (success : FormulaSubstitution.checked replacements input = .ok output) :
    substitute replacements input = output := formula_checked _ _ _ success

/-- The total API inherits simultaneous semantics on the checked-success domain. -/
theorem checked_semantics (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (replacements : List (Name × Term)) (input output : Formula)
    (success : FormulaSubstitution.checked replacements input = .ok output) (env : Name → Value) :
    Holds model env (substitute replacements input) ↔
      Holds model (FormulaSubstitution.assignment model env
        (replacements.filter fun entry => !identityReplacement entry)) input := by
  rw [checked_agrees _ _ _ success]
  exact FormulaCorrectness.checked_semantics model nullary _ _ _ success env

/-- All name substitutions used by guard evaluation use the total public result. -/
theorem guard_substitution (renamed : List (Name × Name)) (input : Formula) :
    substitute (SourceFormula.replacements renamed) input = SourceFormula.substitute renamed input :=
  checked_agrees _ _ _ (SourceFormula.substitute_checked renamed input)

/-- Retaining an unsupported head still substitutes each of its arguments. -/
theorem unsupported_arguments :
    term [("f", .lit 7), ("x", .lit 2)] (.app "f" [.var "x"]) = .app "f" [.lit 2] := by simp [term, arguments, lookup]

/-- An unsupported inner head is checked before the unsupported outer head. -/
theorem inner_error_first :
    FormulaSubstitution.term [("f", .lit 7), ("g", .lit 8)] (.app "f" [.app "g" [.lit 0]]) =
      .error (.unsupportedFunction "g" (.lit 8)) := by
  simp [FormulaSubstitution.term, FormulaSubstitution.arguments, lookup]

/-- The total fallback is not arbitrary simultaneous function-value replacement. -/
theorem unsupported_not_simultaneous :
    let model : Interpretation Int := { integerModel with apply := fun head args => head + args.foldl (· + ·) 0 }
    let env : Name → Int := fun _ => 0
    let active : List (Name × Term) := [("f", .lit 7)]
    evaluateTerm model env (term active (.app "f" [.lit 0])) ≠
      evaluateTerm model (FormulaSubstitution.assignment model env active) (.app "f" [.lit 0]) := by
  simp [term, arguments, lookup, evaluateTerm, evaluateTerms, FormulaSubstitution.assignment, integerModel]

end MicroCFTA.FormulaTotalSubstitution
