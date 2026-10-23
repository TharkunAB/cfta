import MicroCFTA.FormulaOrder

/-!
# Executable full formula simplification

The earlier semantic development uses classical structural equality. This
module replaces only that decision procedure with the proved source order.
The output is exactly equal to the earlier simplifier output.
-/
namespace MicroCFTA.FormulaExecutable
open FullSyntax

/-- Source structural comparison decides full term equality. -/
instance termDecidableEq : DecidableEq Term := fun left right =>
  if same : FormulaOrder.compareTerm left right = .eq then
    .isTrue ((FormulaOrder.term_eq left right).mp same)
  else .isFalse (fun equal => same ((FormulaOrder.term_eq left right).mpr equal))

/-- Source structural comparison decides full formula equality. -/
instance formulaDecidableEq : DecidableEq Formula := fun left right =>
  if same : FormulaOrder.compareFormula left right = .eq then
    .isTrue ((FormulaOrder.formula_eq left right).mp same)
  else .isFalse (fun equal => same ((FormulaOrder.formula_eq left right).mpr equal))

/-- The source tautology test with executable structural equality. -/
def tautology : Formula → Bool
  | .top => true
  | .atom .eq left right | .atom .le left right | .atom .ge left right => decide (left = right)
  | .atom .ne (.lit left) (.lit right) => left != right
  | _ => false

/-- The source contradiction test with executable structural equality. -/
def contradiction : Formula → Bool
  | .bottom => true
  | .atom .eq (.lit left) (.lit right) => left != right
  | .atom .ne left right => decide (left = right)
  | _ => false

theorem tautology_eq (formula : Formula) : tautology formula = FormulaSimplify.tautology formula := by
  cases formula with
  | atom relation left right => cases relation <;> cases left <;> cases right <;>
      apply Bool.eq_iff_iff.mpr <;> simp [tautology, FormulaSimplify.tautology]
  | _ => rfl

theorem contradiction_eq (formula : Formula) : contradiction formula = FormulaSimplify.contradiction formula := by
  cases formula with
  | atom relation left right => cases relation <;> cases left <;> cases right <;>
      apply Bool.eq_iff_iff.mpr <;> simp [contradiction, FormulaSimplify.contradiction]
  | _ => rfl

/-- Use the source constructor order for the canonical conjunction list. -/
def canonical (parts : List Formula) : List Formula :=
  parts.eraseDups.mergeSort (fun left right => (FormulaOrder.compareFormula left right).isLE)

theorem canonical_eq (parts : List Formula) : canonical parts =
    FormulaSimplify.canonical (fun left right => (FormulaOrder.compareFormula left right).isLE) parts := by
  unfold canonical FormulaSimplify.canonical List.eraseDups
  congr
  funext left right
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]

mutual
/-- Execute every source simplifier case with decidable structural comparison. -/
def simplify : Formula → Formula
  | .or [] => .bottom
  | .or [part] => simplify part
  | .not part => FormulaSimplify.simplifyNot (simplify part)
  | .and parts =>
      if parts.any contradiction then .bottom
      else FormulaSimplify.packAnd (canonical (FormulaSimplify.flatten
        ((simplifyParts parts).filter fun part => !tautology part)))
  | .or parts =>
      if parts.any tautology then .top
      else FormulaSimplify.packOr ((simplifyParts parts).filter fun part => !contradiction part)
  | part => if contradiction part then .bottom else if tautology part then .top else part
termination_by part => sizeOf part

/-- Execute the source Boolean-list traversal. -/
def simplifyParts : List Formula → List Formula
  | [] => []
  | part :: rest => simplify part :: simplifyParts rest
termination_by parts => sizeOf parts
end

mutual
/-- The executable simplifier returns exactly the proved source formula. -/
theorem simplify_eq (input : Formula) : simplify input = FormulaOrder.simplify input := by
  cases input with
  | top | bottom | atom _ _ _ | «forall» _ _ | «exists» _ _ =>
      simp [simplify, FormulaOrder.simplify, FormulaSimplify.simplify, contradiction_eq, tautology_eq]
  | and ps =>
      simp [simplify, FormulaOrder.simplify, FormulaSimplify.simplify, simplifyParts_eq ps,
        funext tautology_eq, funext contradiction_eq, canonical_eq]
  | not p =>
      simp [simplify, FormulaOrder.simplify, FormulaSimplify.simplify, simplify_eq p]
  | or ps =>
      cases ps with
      | nil => simp [simplify, FormulaOrder.simplify, FormulaSimplify.simplify]
      | cons p ps =>
          cases ps with
          | nil => simpa [simplify, FormulaOrder.simplify, FormulaSimplify.simplify] using simplify_eq p
          | cons q rest =>
              simp [simplify, FormulaOrder.simplify, FormulaSimplify.simplify, simplifyParts_eq (p :: q :: rest),
                funext tautology_eq, funext contradiction_eq]
termination_by sizeOf input

theorem simplifyParts_eq (parts : List Formula) : simplifyParts parts =
    FormulaSimplify.simplifyParts (fun left right => (FormulaOrder.compareFormula left right).isLE) parts := by
  cases parts with
  | nil => simp [simplifyParts, FormulaSimplify.simplifyParts]
  | cons p ps => simp [simplifyParts, FormulaSimplify.simplifyParts, simplify_eq p,
      FormulaOrder.simplify, simplifyParts_eq ps]
termination_by sizeOf parts
end

/-- Executable simplification has the full formula semantics already proved for the source. -/
theorem simplify_semantics (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (env : Name → Value) (input : Formula) : Holds model env (simplify input) ↔ Holds model env input := by
  rw [simplify_eq]
  exact FormulaOrder.simplify_semantics model laws env input

end MicroCFTA.FormulaExecutable
