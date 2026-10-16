import MicroCFTA.SourceCurrentMeasureEvaluation
import MicroCFTA.FormulaLowering

/-!
# Literal conditional folding in current measures

The source tests the original condition with no leaf values. A known choice
folds only its selected branch. An unknown choice folds its condition and
both branches. Applications, division, modulo, casts, and quantified formula
bodies are unchanged. Full denotation is retained under integer primitive
laws. No property of an arbitrary syntax-sensitive leaf callback is assumed.
-/
namespace MicroCFTA.SourceCurrentMeasureFolding
open FullSyntax

mutual
/-- Fold only the term constructors visited by the source worker. -/
def foldTerm : Term → Term
  | .ite condition yes no => match SourceCurrentMeasureEvaluation.evaluateFormula (fun _ => none) condition with
      | some true => foldTerm yes
      | some false => foldTerm no
      | none => .ite (foldConditionals condition) (foldTerm yes) (foldTerm no)
  | .neg inner => .neg (foldTerm inner)
  | .add left right => .add (foldTerm left) (foldTerm right)
  | .sub left right => .sub (foldTerm left) (foldTerm right)
  | .mul left right => .mul (foldTerm left) (foldTerm right)
  | other => other
termination_by term => sizeOf term

/-- Rebuild supported formula constructors, without entering quantified bodies. -/
def foldConditionals : Formula → Formula
  | .and parts => .and (foldParts parts)
  | .or parts => .or (foldParts parts)
  | .not inner => .not (foldConditionals inner)
  | .atom relation left right => .atom relation (foldTerm left) (foldTerm right)
  | other => other
termination_by formula => sizeOf formula

/-- Fold formula parts in their original finite-list order. -/
def foldParts : List Formula → List Formula
  | [] => []
  | first :: rest => foldConditionals first :: foldParts rest
termination_by parts => sizeOf parts
end

/-- The part worker is exactly the source map operation. -/
theorem foldParts_eq (parts : List Formula) : foldParts parts = parts.map foldConditionals := by
  induction parts with
  | nil => simp only [foldParts, List.map_nil]
  | cons first rest ih => simp only [foldParts, List.map_cons, ih]

variable (model : Interpretation Value) (integer : Int → Value) (env : Name → Value)

mutual
/-- Every folded term retains its full denotation, including unsupported unchanged terms. -/
theorem term_exact (laws : SourceCurrentMeasureEvaluation.IntegerLaws model integer) (term : Term) :
    FullSyntax.evaluateTerm model env (foldTerm term) = FullSyntax.evaluateTerm model env term := by
  cases term with
  | lit | var | app | div | mod | cast => simp only [foldTerm]
  | neg inner => simp only [foldTerm, FullSyntax.evaluateTerm, term_exact laws inner]
  | add left right | sub left right | mul left right =>
      simp only [foldTerm, FullSyntax.evaluateTerm, term_exact laws left, term_exact laws right]
  | ite condition yes no =>
      cases tested : SourceCurrentMeasureEvaluation.evaluateFormula (fun _ => none) condition with
      | none =>
          have same := formula_exact laws condition
          simp only [foldTerm, tested, FullSyntax.evaluateTerm, term_exact laws yes, term_exact laws no]
          rw [propext same]
      | some choice =>
          have correct := SourceCurrentMeasureEvaluation.formula_sound model integer env (fun _ => none) laws (SourceCurrentMeasureEvaluation.none_agrees model integer env) condition choice tested
          cases choice with
          | false =>
              have failed : ¬Holds model env condition := by simpa using correct
              simp only [foldTerm, tested, FullSyntax.evaluateTerm, failed, ite_false, term_exact laws no]
          | true =>
              have holds : Holds model env condition := correct.mpr rfl
              simp only [foldTerm, tested, FullSyntax.evaluateTerm, holds, ite_true, term_exact laws yes]
termination_by sizeOf term

/-- Conditional folding preserves classical full-formula truth. -/
theorem formula_exact (laws : SourceCurrentMeasureEvaluation.IntegerLaws model integer) (formula : Formula) :
    Holds model env (foldConditionals formula) ↔ Holds model env formula := by
  cases formula with
  | top | bottom | «forall» | «exists» => simp only [foldConditionals]
  | and parts => simpa only [foldConditionals, Holds] using all_exact laws parts
  | or parts => simpa only [foldConditionals, Holds] using any_exact laws parts
  | not inner => simp only [foldConditionals, Holds, formula_exact laws inner]
  | atom relation left right => simp only [foldConditionals, Holds, term_exact laws left, term_exact laws right]
termination_by sizeOf formula

/-- Folding retains conjunction order and truth for every part. -/
theorem all_exact (laws : SourceCurrentMeasureEvaluation.IntegerLaws model integer) (parts : List Formula) :
    holdsAll model env (foldParts parts) ↔ holdsAll model env parts := by
  cases parts with
  | nil => simp only [foldParts]
  | cons first rest => simp only [foldParts, holdsAll, formula_exact laws first, all_exact laws rest]
termination_by sizeOf parts

/-- Folding retains disjunction order and truth for every part. -/
theorem any_exact (laws : SourceCurrentMeasureEvaluation.IntegerLaws model integer) (parts : List Formula) :
    holdsAny model env (foldParts parts) ↔ holdsAny model env parts := by
  cases parts with
  | nil => simp only [foldParts]
  | cons first rest => simp only [foldParts, holdsAny, formula_exact laws first, any_exact laws rest]
termination_by sizeOf parts
end

/-- The existing solver-expression lowering retains the proved term equality. -/
theorem lowered_term_exact (target : FormulaLowering.Model Value) (integer : Int → Value) (env : Name → Value)
    (laws : SourceCurrentMeasureEvaluation.IntegerLaws (FormulaLowering.sourceModel target) integer) (term : Term) :
    FormulaLowering.evaluate target env (FormulaLowering.lowerTerm (foldTerm term)) =
      FormulaLowering.evaluate target env (FormulaLowering.lowerTerm term) := by
  rw [FormulaLowering.term_lower, FormulaLowering.term_lower]
  exact term_exact (FormulaLowering.sourceModel target) integer env laws term

/-- The existing solver-expression lowering retains the proved formula equivalence. -/
theorem lowered_formula_exact (target : FormulaLowering.Model Value) (integer : Int → Value) (env : Name → Value)
    (laws : SourceCurrentMeasureEvaluation.IntegerLaws (FormulaLowering.sourceModel target) integer) (formula : Formula) :
    FormulaLowering.Holds target env (FormulaLowering.lowerFormula (foldConditionals formula)) ↔
      FormulaLowering.Holds target env (FormulaLowering.lowerFormula formula) := by
  rw [FormulaLowering.formula_lower, FormulaLowering.formula_lower]
  exact formula_exact (FormulaLowering.sourceModel target) integer env laws formula

end MicroCFTA.SourceCurrentMeasureFolding
