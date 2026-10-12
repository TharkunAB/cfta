import MicroCFTA.SourceReadLogicalIntegerAdapter

/-!
# Concrete integer arithmetic through the pure adapter

The target interpretation uses unbounded integers. Its induced source model
agrees with the existing integer model on every embedded arithmetic-core
query. This theorem does not identify the two models on all raw sort syntax.
External Sat and Unsat correctness remains an explicit solver boundary.
-/
namespace MicroCFTA.SourceReadLogicalIntegerCore
open FullSyntax SourceReadLogicalIntegerAdapter

/-- A target interpretation for the source integer arithmetic fragment. -/
def integerTarget : FormulaLowering.Model Int where
  literal := id
  neg := (- ·)
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := Int.ediv
  mod := Int.emod
  apply := fun _ _ => 0
  cast := fun value _ => value
  hasSort := fun sort value => match sort with
    | .int => True
    | .bool => value = 0 ∨ value = 1
    | .real | .arrow _ _ => False
  relation := fun relation left right => CoreFormula.evalRelation relation left right = true

/-- Int declarations admit every integer value. -/
theorem all_integers (value : Int) : integerTarget.hasSort .int value := trivial

/-- Integer relations meet the formula simplifier's semantic laws. -/
theorem relation_laws : FormulaSimplify.RelationLaws (FormulaLowering.sourceModel integerTarget) := by
  constructor <;> intros <;> simp_all [FormulaLowering.sourceModel, integerTarget, CoreFormula.evalRelation]

mutual
/-- The full syntax's integer interpretation preserves the earlier term semantics. -/
theorem core_term (env : Name → Int) (t : CoreFormula.Term) :
    evaluateTerm (FormulaLowering.sourceModel integerTarget) env (embedTerm t) = CoreFormula.evalTerm env t := by
  cases t with
  | lit n => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm] <;> rfl
  | var n => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm] <;> rfl
  | neg t => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm, core_term env t] <;> rfl
  | add t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      core_term env t, core_term env u] <;> rfl
  | sub t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      core_term env t, core_term env u] <;> rfl
  | mul t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      core_term env t, core_term env u] <;> rfl
  | ite p t u => simp [embedTerm, evaluateTerm, CoreFormula.evalTerm,
      core_formula env p, core_term env t, core_term env u] <;> rfl
termination_by sizeOf t

/-- Full classical truth agrees with the earlier executable core truth. -/
theorem core_formula (env : Name → Int) (p : CoreFormula.Formula) :
    Holds (FormulaLowering.sourceModel integerTarget) env (embedFormula p) ↔ CoreFormula.evalFormula env p = true := by
  cases p with
  | top => simp [embedFormula, Holds, CoreFormula.evalFormula] <;> rfl
  | bottom => simp [embedFormula, Holds, CoreFormula.evalFormula] <;> rfl
  | and ps => simp [embedFormula, Holds, CoreFormula.evalFormula, core_all env ps] <;> rfl
  | or ps => simp [embedFormula, Holds, CoreFormula.evalFormula, core_any env ps] <;> rfl
  | not p => simp [embedFormula, Holds, CoreFormula.evalFormula, core_formula env p] <;> rfl
  | atom r t u => simp [embedFormula, Holds, CoreFormula.evalFormula,
      core_term env t, core_term env u] <;> rfl
termination_by sizeOf p

/-- Conjunction lists retain every truth condition under embedding. -/
theorem core_all (env : Name → Int) (ps : List CoreFormula.Formula) :
    holdsAll (FormulaLowering.sourceModel integerTarget) env (embedParts ps) ↔ CoreFormula.evalAll env ps = true := by
  cases ps with
  | nil => simp [embedParts, holdsAll, CoreFormula.evalAll] <;> rfl
  | cons p ps => simp [embedParts, holdsAll, CoreFormula.evalAll,
      core_formula env p, core_all env ps] <;> rfl
termination_by sizeOf ps

/-- Disjunction lists retain every truth condition under embedding. -/
theorem core_any (env : Name → Int) (ps : List CoreFormula.Formula) :
    holdsAny (FormulaLowering.sourceModel integerTarget) env (embedParts ps) ↔ CoreFormula.evalAny env ps = true := by
  cases ps with
  | nil => simp [embedParts, holdsAny, CoreFormula.evalAny] <;> rfl
  | cons p ps => simp [embedParts, holdsAny, CoreFormula.evalAny,
      core_formula env p, core_any env ps] <;> rfl
termination_by sizeOf ps
end

/-- The actual induced source model agrees with integerModel throughout the arithmetic core. -/
theorem core_agreement (env : Name → Int) (formula : CoreFormula.Formula) :
    Holds (FormulaLowering.sourceModel integerTarget) env (embedFormula formula) ↔
      Holds integerModel env (embedFormula formula) :=
  (core_formula env formula).trans (FullSyntax.embedFormula_holds env formula).symm

/-- A returned pure-adapter answer has the existing integer meaning on every arithmetic-core query. -/
theorem returned_core_supports (given : List SolverAdapter.Declaration) (integer : IntegerDeclarations given)
    (bindings : List (Name × Name)) (antecedent consequent : CoreFormula.Formula)
    (milliseconds : Int) (check : SolverAdapter.Prepared → SolverAdapter.Attempt)
    (correct : ∀ request response reached, check request = .answered response reached →
      SolverAdapter.ResponseCorrect integerTarget request response)
    (verdict : Guards.Verdict)
    (returned : (SolverAdapter.execute given bindings [] (embedFormula antecedent) (embedFormula consequent)
      milliseconds check).result = .returned verdict) :
    Guards.Supports verdict (SourceEntailment.Entails integerModel (fun _ => True)
      (embedFormula antecedent) (embedFormula consequent)) := by
  have support := returned_supports integerTarget all_integers given integer bindings
    (embedFormula antecedent) (embedFormula consequent) milliseconds check correct verdict returned
  cases verdict with
  | unknown => trivial
  | yes =>
      intro env _ assumed
      exact (core_agreement env consequent).mp (support env trivial ((core_agreement env antecedent).mpr assumed))
  | no =>
      intro proved
      apply support
      intro env _ assumed
      exact (core_agreement env consequent).mpr (proved env trivial ((core_agreement env antecedent).mp assumed))

end MicroCFTA.SourceReadLogicalIntegerCore
