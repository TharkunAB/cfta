import MicroCFTA.FormulaCorrectness

/-!
# Liquid Fixpoint formula lowering

This is the emitted subset of `LiquidFixpoint.toFixpoint`, `termToFixpoint`,
and `sortToFixpoint`. The target splits the value and predicate views of
Fixpoint `Expr`. Application uses the actual left fold of `eApps`. Function
sorts use the right-nested `FFunc` form of `mkFFunc 0` in version 0.9.6.3.7.
An interpretation supplies the target primitive meanings and sort domains.
This module does not verify the external solver or the SMT serializer.
-/

namespace MicroCFTA.FormulaLowering

open FullSyntax

/-- The target sorts emitted by this library. -/
inductive TargetSort where
  | int | real | bool
  | arrow (argument result : TargetSort)
  deriving DecidableEq, Repr

mutual
/-- The source sort translation, including the normalization of zero-argument function sorts. -/
def lowerSort : ValueSort → TargetSort
  | .int => .int
  | .real => .real
  | .bool => .bool
  | .function arguments result => lowerArguments arguments (lowerSort result)
termination_by sort => sizeOf sort

/-- Build the target function arrows in argument order. -/
def lowerArguments : List ValueSort → TargetSort → TargetSort
  | [], result => result
  | argument :: rest, result => .arrow (lowerSort argument) (lowerArguments rest result)
termination_by arguments _ => sizeOf arguments
end

/-- A target sort has a canonical source representation with one argument per function sort. -/
def raiseSort : TargetSort → ValueSort
  | .int => .int
  | .real => .real
  | .bool => .bool
  | .arrow argument result => .function [raiseSort argument] (raiseSort result)

/-- Every target sort is represented exactly by its canonical source sort. -/
theorem lower_raise (sort : TargetSort) : lowerSort (raiseSort sort) = sort := by
  induction sort with
  | int | real | bool => simp [raiseSort, lowerSort]
  | arrow argument result ha hr => simp [raiseSort, lowerSort, lowerArguments, ha, hr]

/-- The source sort normalization induced by `mkFFunc 0`. -/
def normalizeSort (sort : ValueSort) : ValueSort := raiseSort (lowerSort sort)

/-- Sort normalization is stable after its first pass. -/
theorem normalizeSort_idempotent (sort : ValueSort) : normalizeSort (normalizeSort sort) = normalizeSort sort := by
  simp [normalizeSort, lower_raise]

/-- A zero-argument function sort is exactly its result sort at the target interface. -/
theorem nullary_sort (sort : ValueSort) : lowerSort (.function [] sort) = lowerSort sort := by
  simp [lowerSort, lowerArguments]

/-- The five target binary arithmetic operators emitted by the source. -/
inductive Arithmetic where
  | plus | minus | times | div | mod
  deriving DecidableEq, Repr

mutual
/-- Value-expression constructors in the emitted Fixpoint subset. -/
inductive Term where
  | integer (value : Int)
  | variable (name : Name)
  | negative (inner : Term)
  | binary (operator : Arithmetic) (left right : Term)
  | application (function argument : Term)
  | conditional (condition : Formula) (yes no : Term)
  | cast (inner : Term) (sort : TargetSort)
  deriving Repr

/-- Predicate-expression constructors in the emitted Fixpoint subset. -/
inductive Formula where
  | true | false
  | and (parts : List Formula)
  | or (parts : List Formula)
  | not (inner : Formula)
  | atom (relation : Relation) (left right : Term)
  | forall (bound : List (Name × TargetSort)) (inner : Formula)
  | exists (bound : List (Name × TargetSort)) (inner : Formula)
  deriving Repr
end

mutual
/-- Translate all source terms in the exact constructor cases of `termToFixpoint`. -/
def lowerTerm : FullSyntax.Term → Term
  | .lit value => .integer value
  | .var name => .variable name
  | .app name arguments => lowerApps (.variable name) arguments
  | .neg inner => .negative (lowerTerm inner)
  | .add left right => .binary .plus (lowerTerm left) (lowerTerm right)
  | .sub left right => .binary .minus (lowerTerm left) (lowerTerm right)
  | .mul left right => .binary .times (lowerTerm left) (lowerTerm right)
  | .div left right => .binary .div (lowerTerm left) (lowerTerm right)
  | .mod left right => .binary .mod (lowerTerm left) (lowerTerm right)
  | .ite condition yes no => .conditional (lowerFormula condition) (lowerTerm yes) (lowerTerm no)
  | .cast inner sort => .cast (lowerTerm inner) (lowerSort sort)
termination_by term => sizeOf term

/-- `eApps` is a left fold of binary application, including the unchanged empty case. -/
def lowerApps (function : Term) : List FullSyntax.Term → Term
  | [] => function
  | argument :: rest => lowerApps (.application function (lowerTerm argument)) rest
termination_by arguments => sizeOf arguments

/-- Translate every source predicate constructor and every sorted binder. -/
def lowerFormula : FullSyntax.Formula → Formula
  | .top => .true
  | .bottom => .false
  | .and parts => .and (lowerParts parts)
  | .or parts => .or (lowerParts parts)
  | .not inner => .not (lowerFormula inner)
  | .atom relation left right => .atom relation (lowerTerm left) (lowerTerm right)
  | .forall bound inner => .forall (bound.map fun (name, sort) => (name, lowerSort sort)) (lowerFormula inner)
  | .exists bound inner => .exists (bound.map fun (name, sort) => (name, lowerSort sort)) (lowerFormula inner)
termination_by formula => sizeOf formula

/-- Translate Boolean list parts in source order. -/
def lowerParts : List FullSyntax.Formula → List Formula
  | [] => []
  | part :: rest => lowerFormula part :: lowerParts rest
termination_by parts => sizeOf parts
end

/-- Primitive meanings for the emitted target expression subset. -/
structure Model (Value : Type) where
  literal : Int → Value
  neg : Value → Value
  add : Value → Value → Value
  sub : Value → Value → Value
  mul : Value → Value → Value
  div : Value → Value → Value
  mod : Value → Value → Value
  apply : Value → Value → Value
  cast : Value → TargetSort → Value
  hasSort : TargetSort → Value → Prop
  relation : Relation → Value → Value → Prop

/-- The source interpretation induced by the target primitives and actual sort lowering. -/
def sourceModel (model : Model Value) : Interpretation Value where
  literal := model.literal
  neg := model.neg
  add := model.add
  sub := model.sub
  mul := model.mul
  div := model.div
  mod := model.mod
  apply := fun function arguments => arguments.foldl model.apply function
  cast := fun value sort => model.cast value (lowerSort sort)
  hasSort := fun sort value => model.hasSort (lowerSort sort) value
  relation := model.relation

/-- Interpret a binary arithmetic operator. -/
def arithmetic (model : Model Value) : Arithmetic → Value → Value → Value
  | .plus => model.add
  | .minus => model.sub
  | .times => model.mul
  | .div => model.div
  | .mod => model.mod

/-- Interpret the emitted universal sorted binder list. -/
def allBound (model : Model Value) : List (Name × TargetSort) → (Name → Value) → ((Name → Value) → Prop) → Prop
  | [], env, body => body env
  | (name, sort) :: rest, env, body =>
      ∀ value, model.hasSort sort value → allBound model rest (update env name value) body

/-- Interpret the emitted existential sorted binder list. -/
def someBound (model : Model Value) : List (Name × TargetSort) → (Name → Value) → ((Name → Value) → Prop) → Prop
  | [], env, body => body env
  | (name, sort) :: rest, env, body =>
      ∃ value, model.hasSort sort value ∧ someBound model rest (update env name value) body

noncomputable section
open Classical in
mutual
/-- Evaluate the value view of the emitted Fixpoint expression. -/
def evaluate (model : Model Value) (env : Name → Value) : Term → Value
  | .integer value => model.literal value
  | .variable name => env name
  | .negative inner => model.neg (evaluate model env inner)
  | .binary operator left right => arithmetic model operator (evaluate model env left) (evaluate model env right)
  | .application function argument => model.apply (evaluate model env function) (evaluate model env argument)
  | .conditional condition yes no => if Holds model env condition then evaluate model env yes else evaluate model env no
  | .cast inner sort => model.cast (evaluate model env inner) sort
termination_by term => sizeOf term

/-- Evaluate the predicate view of the emitted Fixpoint expression. -/
def Holds (model : Model Value) (env : Name → Value) : Formula → Prop
  | .true => True
  | .false => False
  | .and parts => holdsAll model env parts
  | .or parts => holdsAny model env parts
  | .not inner => ¬Holds model env inner
  | .atom relation left right => model.relation relation (evaluate model env left) (evaluate model env right)
  | .forall bound inner => allBound model bound env (fun assigned => Holds model assigned inner)
  | .exists bound inner => someBound model bound env (fun assigned => Holds model assigned inner)
termination_by formula => sizeOf formula

/-- Every emitted conjunction part holds. -/
def holdsAll (model : Model Value) (env : Name → Value) : List Formula → Prop
  | [] => True
  | part :: rest => Holds model env part ∧ holdsAll model env rest
termination_by parts => sizeOf parts

/-- At least one emitted disjunction part holds. -/
def holdsAny (model : Model Value) (env : Name → Value) : List Formula → Prop
  | [] => False
  | part :: rest => Holds model env part ∨ holdsAny model env rest
termination_by parts => sizeOf parts
end
end

/-- Sort translation retains the domain and order of every universal binder. -/
theorem allBound_lower (model : Model Value) (bound : List (Name × ValueSort))
    (env : Name → Value) (body : (Name → Value) → Prop) :
    allBound model (bound.map fun (name, sort) => (name, lowerSort sort)) env body ↔
      FullSyntax.allBound (sourceModel model) bound env body := by
  induction bound generalizing env with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [List.map_cons, allBound, FullSyntax.allBound, sourceModel]
      apply forall_congr'
      intro value
      exact imp_congr_right (fun _ => ih _)

/-- Sort translation retains the domain and order of every existential binder. -/
theorem someBound_lower (model : Model Value) (bound : List (Name × ValueSort))
    (env : Name → Value) (body : (Name → Value) → Prop) :
    someBound model (bound.map fun (name, sort) => (name, lowerSort sort)) env body ↔
      FullSyntax.someBound (sourceModel model) bound env body := by
  induction bound generalizing env with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, sort⟩
      simp only [List.map_cons, someBound, FullSyntax.someBound, sourceModel]
      apply exists_congr
      intro value
      exact and_congr_right (fun _ => ih _)

mutual
/-- Every source value expression has exactly the meaning of its emitted target expression. -/
theorem term_lower (model : Model Value) (input : FullSyntax.Term) (env : Name → Value) :
    evaluate model env (lowerTerm input) = evaluateTerm (sourceModel model) env input := by
  cases input with
  | lit value | var value => simp [lowerTerm, evaluate, evaluateTerm, sourceModel]
  | app name arguments =>
      simp only [lowerTerm, evaluateTerm, sourceModel]
      simpa only [evaluate, sourceModel] using apps_lower model arguments (.variable name) env
  | neg inner => simp only [lowerTerm, evaluate, evaluateTerm, sourceModel, term_lower model inner env]
  | add left right | sub left right | mul left right | div left right | mod left right =>
      simp only [lowerTerm, evaluate, evaluateTerm, sourceModel, arithmetic,
        term_lower model left env, term_lower model right env]
  | cast inner sort => simp only [lowerTerm, evaluate, evaluateTerm, sourceModel, term_lower model inner env]
  | ite condition yes no =>
      simp only [lowerTerm, evaluate, evaluateTerm, term_lower model yes env, term_lower model no env]
      have same := formula_lower model condition env
      by_cases true : Holds model env (lowerFormula condition)
      · simp [true, same.mp true]
      · have false : ¬FullSyntax.Holds (sourceModel model) env condition := fun yes => true (same.mpr yes)
        simp [true, false]
termination_by sizeOf input

/-- The emitted left-associated applications preserve the source argument order and nullary behavior. -/
theorem apps_lower (model : Model Value) (arguments : List FullSyntax.Term) (function : Term) (env : Name → Value) :
    evaluate model env (lowerApps function arguments) =
      (evaluateTerms (sourceModel model) env arguments).foldl model.apply (evaluate model env function) := by
  cases arguments with
  | nil => simp [lowerApps, evaluateTerms]
  | cons argument rest =>
      simp only [lowerApps, evaluateTerms, List.foldl_cons]
      rw [apps_lower model rest (.application function (lowerTerm argument)) env]
      simp only [evaluate, term_lower model argument env]
termination_by sizeOf arguments

/-- Every source predicate has exactly the truth value of its emitted target predicate. -/
theorem formula_lower (model : Model Value) (input : FullSyntax.Formula) (env : Name → Value) :
    Holds model env (lowerFormula input) ↔ FullSyntax.Holds (sourceModel model) env input := by
  cases input with
  | top | bottom => simp [lowerFormula, Holds, FullSyntax.Holds]
  | and parts | or parts =>
      have both := parts_lower model parts env
      simp only [lowerFormula, Holds, FullSyntax.Holds]
      first | exact both.1 | exact both.2
  | not inner =>
      simpa only [lowerFormula, Holds, FullSyntax.Holds] using not_congr (formula_lower model inner env)
  | atom relation left right =>
      simp only [lowerFormula, Holds, FullSyntax.Holds, sourceModel,
        term_lower model left env, term_lower model right env]
  | «forall» bound inner =>
      simp only [lowerFormula, Holds, FullSyntax.Holds]
      have body : (fun assigned => Holds model assigned (lowerFormula inner)) =
          (fun assigned => FullSyntax.Holds (sourceModel model) assigned inner) :=
        funext (fun assigned => propext (formula_lower model inner assigned))
      rw [body]
      exact allBound_lower model bound env _
  | «exists» bound inner =>
      simp only [lowerFormula, Holds, FullSyntax.Holds]
      have body : (fun assigned => Holds model assigned (lowerFormula inner)) =
          (fun assigned => FullSyntax.Holds (sourceModel model) assigned inner) :=
        funext (fun assigned => propext (formula_lower model inner assigned))
      rw [body]
      exact someBound_lower model bound env _
termination_by sizeOf input

/-- Predicate-list lowering preserves both conjunction and disjunction. -/
theorem parts_lower (model : Model Value) (parts : List FullSyntax.Formula) (env : Name → Value) :
    (holdsAll model env (lowerParts parts) ↔ FullSyntax.holdsAll (sourceModel model) env parts) ∧
      (holdsAny model env (lowerParts parts) ↔ FullSyntax.holdsAny (sourceModel model) env parts) := by
  cases parts with
  | nil => simp [lowerParts, holdsAll, holdsAny, FullSyntax.holdsAll, FullSyntax.holdsAny]
  | cons part rest =>
      have hp := formula_lower model part env
      have hs := parts_lower model rest env
      simp only [lowerParts, holdsAll, holdsAny, FullSyntax.holdsAll, FullSyntax.holdsAny,
        hp, hs.1, hs.2, iff_self, and_self]
termination_by sizeOf parts
end

/-- The nullary-application law required by checked substitution follows from the actual application lowering. -/
theorem sourceModel_nullary (model : Model Value) (value : Value) : (sourceModel model).apply value [] = value := rfl

/-- Repaired checked substitution and actual target lowering preserve the same simultaneous substitution semantics. -/
theorem checked_lower (model : Model Value) (replacements : List (Name × FullSyntax.Term))
    (input output : FullSyntax.Formula)
    (success : FormulaSubstitution.checked replacements input = .ok output) (env : Name → Value) :
    Holds model env (lowerFormula output) ↔ Holds model
      (FormulaSubstitution.assignment (sourceModel model) env
        (replacements.filter fun entry => !identityReplacement entry)) (lowerFormula input) := by
  exact (formula_lower model output env).trans
    ((FormulaCorrectness.checked_semantics (sourceModel model) (sourceModel_nullary model)
      replacements input output success env).trans (formula_lower model input _).symm)

end MicroCFTA.FormulaLowering
