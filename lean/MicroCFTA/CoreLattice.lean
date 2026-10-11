import MicroCFTA.CoreFormula
import MicroCFTA.LatticeFormula

/-!
# Core formulas and the checked integer lattice compiler

This module connects the integer fragment of `Data.CFTA.Formula` to the
existing lattice proofs. `FullSyntax` supplies the current complete syntax.
Every core constructor has an explicit translation. A conditional term maps
to the parser's unsupported arithmetic case, as in `linearTerm`. Formula
lists expand to the same right folds as the source's `signed` function.

The correctness theorem uses the total core semantics. It does not assume
that a formula has its desired meaning, or that its compilation is exact.
The existing lattice error type abstracts the offending term in an error.
-/

namespace MicroCFTA.CoreLattice
open CoreFormula

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- Translate each of the six core relations to the checked atom compiler. -/
def lowerRelation : CoreFormula.Relation → LatticeSigned.Relation
  | .eq => .eq | .ne => .ne | .gt => .gt | .ge => .ge | .lt => .lt | .le => .le

/-- Relation translation preserves all integer comparisons. -/
theorem lowerRelation_correct (r : CoreFormula.Relation) (a b : Int) :
    LatticeSigned.relationHolds (lowerRelation r) a b = evalRelation r a b := by
  cases r <;> apply Bool.eq_iff_iff.mpr <;>
    simp [lowerRelation, LatticeSigned.relationHolds, evalRelation]

/-- Translate integer syntax. Conditional terms are rejected by the source parser. -/
def lowerTerm : Term → LatticeLinear.Expr Name
  | .lit n => .integer n
  | .var name => .name name
  | .neg t => .neg (lowerTerm t)
  | .add t u => .add (lowerTerm t) (lowerTerm u)
  | .sub t u => .sub (lowerTerm t) (lowerTerm u)
  | .mul t u => .mul (lowerTerm t) (lowerTerm u)
  | .ite _ _ _ => .unsupported

/-- Whether term evaluation in the lattice syntax has no unsupported conditional. -/
def arithmeticSupported : Term → Bool
  | .lit _ | .var _ => true
  | .neg t => arithmeticSupported t
  | .add t u | .sub t u | .mul t u => arithmeticSupported t && arithmeticSupported u
  | .ite _ _ _ => false

/-- Translation preserves arithmetic meaning whenever its syntax is supported. -/
theorem lowerTerm_evaluation (env : Name → Int) (t : Term) :
    LatticeLinear.evalExpr env (lowerTerm t) =
      if arithmeticSupported t then some (evalTerm env t) else none := by
  cases t with
  | lit n => simp [lowerTerm, LatticeLinear.evalExpr, arithmeticSupported, evalTerm]
  | var n => simp [lowerTerm, LatticeLinear.evalExpr, arithmeticSupported, evalTerm]
  | neg t =>
      rw [lowerTerm, LatticeLinear.evalExpr, lowerTerm_evaluation env t]
      cases h : arithmeticSupported t <;> simp [arithmeticSupported, evalTerm, h]
  | add t u =>
      simp only [lowerTerm, LatticeLinear.evalExpr, lowerTerm_evaluation env t,
        lowerTerm_evaluation env u]
      cases h : arithmeticSupported t <;> cases k : arithmeticSupported u <;>
        simp [arithmeticSupported, evalTerm, h, k]
  | sub t u =>
      simp only [lowerTerm, LatticeLinear.evalExpr, lowerTerm_evaluation env t,
        lowerTerm_evaluation env u]
      cases h : arithmeticSupported t <;> cases k : arithmeticSupported u <;>
        simp [arithmeticSupported, evalTerm, h, k]
  | mul t u =>
      simp only [lowerTerm, LatticeLinear.evalExpr, lowerTerm_evaluation env t,
        lowerTerm_evaluation env u]
      cases h : arithmeticSupported t <;> cases k : arithmeticSupported u <;>
        simp [arithmeticSupported, evalTerm, h, k]
  | ite p t u => simp [lowerTerm, LatticeLinear.evalExpr, arithmeticSupported]
termination_by sizeOf t

mutual
/-- Translate the entire core Boolean syntax without logical simplification. -/
def lowerFormula : CoreFormula.Formula → LatticeFormula.Formula Name
  | .top => .top
  | .bottom => .bottom
  | .and ps => lowerAll ps
  | .or ps => lowerAny ps
  | .not p => .neg (lowerFormula p)
  | .atom r t u => .atom (lowerRelation r) (lowerTerm t) (lowerTerm u)
termination_by p => sizeOf p

/-- Expand source conjunction lists with their exact right-fold identity. -/
def lowerAll : List CoreFormula.Formula → LatticeFormula.Formula Name
  | [] => .top
  | p :: ps => .conj (lowerFormula p) (lowerAll ps)
termination_by ps => sizeOf ps

/-- Expand source disjunction lists with their exact right-fold identity. -/
def lowerAny : List CoreFormula.Formula → LatticeFormula.Formula Name
  | [] => .bottom
  | p :: ps => .disj (lowerFormula p) (lowerAny ps)
termination_by ps => sizeOf ps
end

mutual
/-- Whether every formula term has supported arithmetic syntax. -/
def formulaSupported : CoreFormula.Formula → Bool
  | .top | .bottom => true
  | .and ps | .or ps => partsSupported ps
  | .not p => formulaSupported p
  | .atom _ t u => arithmeticSupported t && arithmeticSupported u
termination_by p => sizeOf p

/-- Whether all list parts have supported arithmetic syntax. -/
def partsSupported : List CoreFormula.Formula → Bool
  | [] => true
  | p :: ps => formulaSupported p && partsSupported ps
termination_by ps => sizeOf ps
end

mutual
/-- Formula translation agrees with the total core semantics on its supported syntax. -/
theorem lowerFormula_evaluation (env : Name → Int) (p : CoreFormula.Formula) :
    LatticeFormula.evaluateFormula env (lowerFormula p) =
      if formulaSupported p then some (evalFormula env p) else none := by
  cases p with
  | top => simp [lowerFormula, LatticeFormula.evaluateFormula, formulaSupported, evalFormula]
  | bottom => simp [lowerFormula, LatticeFormula.evaluateFormula, formulaSupported, evalFormula]
  | and ps => simp [lowerFormula, formulaSupported, evalFormula, lowerAll_evaluation env ps]
  | or ps => simp [lowerFormula, formulaSupported, evalFormula, lowerAny_evaluation env ps]
  | not p =>
      simp only [lowerFormula, LatticeFormula.evaluateFormula, lowerFormula_evaluation env p]
      cases h : formulaSupported p <;> simp [formulaSupported, evalFormula, h]
  | atom r t u =>
      simp only [lowerFormula, LatticeFormula.evaluateFormula, lowerTerm_evaluation env t,
        lowerTerm_evaluation env u]
      cases h : arithmeticSupported t <;> cases k : arithmeticSupported u <;>
        simp [formulaSupported, evalFormula, h, k, lowerRelation_correct]
termination_by sizeOf p

/-- Expanded conjunctions preserve their complete core meaning. -/
theorem lowerAll_evaluation (env : Name → Int) (ps : List CoreFormula.Formula) :
    LatticeFormula.evaluateFormula env (lowerAll ps) =
      if partsSupported ps then some (evalAll env ps) else none := by
  cases ps with
  | nil => simp [lowerAll, LatticeFormula.evaluateFormula, partsSupported, evalAll]
  | cons p ps =>
      simp only [lowerAll, LatticeFormula.evaluateFormula, lowerFormula_evaluation env p,
        lowerAll_evaluation env ps]
      cases h : formulaSupported p <;> cases k : partsSupported ps <;>
        simp [partsSupported, evalAll, h, k]
termination_by sizeOf ps

/-- Expanded disjunctions preserve their complete core meaning. -/
theorem lowerAny_evaluation (env : Name → Int) (ps : List CoreFormula.Formula) :
    LatticeFormula.evaluateFormula env (lowerAny ps) =
      if partsSupported ps then some (evalAny env ps) else none := by
  cases ps with
  | nil => simp [lowerAny, LatticeFormula.evaluateFormula, partsSupported, evalAny]
  | cons p ps =>
      simp only [lowerAny, LatticeFormula.evaluateFormula, lowerFormula_evaluation env p,
        lowerAny_evaluation env ps]
      cases h : formulaSupported p <;> cases k : partsSupported ps <;>
        simp [partsSupported, evalAny, h, k]
termination_by sizeOf ps
end

/-- The conjunction expansion is exactly the existing source-fold representation. -/
theorem lowerAll_eq (ps : List CoreFormula.Formula) :
    lowerAll ps = LatticeFormula.all (ps.map lowerFormula) := by
  induction ps with
  | nil => simp [lowerAll, LatticeFormula.all]
  | cons p ps ih => simp [lowerAll, LatticeFormula.all, ih]

/-- The disjunction expansion is exactly the existing source-fold representation. -/
theorem lowerAny_eq (ps : List CoreFormula.Formula) :
    lowerAny ps = LatticeFormula.any (ps.map lowerFormula) := by
  induction ps with
  | nil => simp [lowerAny, LatticeFormula.any]
  | cons p ps ih => simp [lowerAny, LatticeFormula.any, ih]

/-- Compile the actual core formula through the proved lattice implementation. -/
def signed (variableOf : Name → Option Nat) (positive : Bool) (p : CoreFormula.Formula) :
    Except (LatticeFormula.Error Name) LatticeSigned.Checked :=
  LatticeFormula.signed variableOf positive (lowerFormula p)

/-- Core conjunction compilation is the source traversal followed by its signed fold. -/
theorem signed_and (variableOf : Name → Option Nat) (positive : Bool)
    (ps : List CoreFormula.Formula) :
    signed variableOf positive (.and ps) =
      LatticeFormula.signedAll variableOf positive (ps.map lowerFormula) := by
  simp [signed, lowerFormula, lowerAll_eq, LatticeFormula.signed_all_eq]

/-- Core disjunction compilation is the source traversal followed by its signed fold. -/
theorem signed_or (variableOf : Name → Option Nat) (positive : Bool)
    (ps : List CoreFormula.Formula) :
    signed variableOf positive (.or ps) =
      LatticeFormula.signedAny variableOf positive (ps.map lowerFormula) := by
  simp [signed, lowerFormula, lowerAny_eq, LatticeFormula.signed_any_eq]

/-- Successful core compilation gives exactly the core formula's zero-or-one indicator. -/
theorem signed_correct (variableOf : Name → Option Nat) (env : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → env name = assignment index)
    (p : CoreFormula.Formula) (positive : Bool) (result : LatticeSigned.Checked)
    (success : signed variableOf positive p = .ok result) :
    LatticeSigned.score assignment result.terms =
      Lattice.indicator (evalFormula env p == positive) := by
  obtain ⟨value, interpreted, counted⟩ :=
    LatticeFormula.signed_correct variableOf env assignment environment
      (lowerFormula p) positive result success
  rw [lowerFormula_evaluation] at interpreted
  cases h : formulaSupported p <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at interpreted
  · cases interpreted
  · have hv := Option.some.inj interpreted
    simpa [hv] using counted

/-- Positive core compilation counts every satisfying assignment once and every other one zero times. -/
theorem signed_indicator (variableOf : Name → Option Nat) (env : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → env name = assignment index)
    (p : CoreFormula.Formula) (result : LatticeSigned.Checked)
    (success : signed variableOf true p = .ok result) :
    LatticeSigned.score assignment result.terms = if evalFormula env p then 1 else 0 := by
  simpa [Lattice.indicator] using
    signed_correct variableOf env assignment environment p true result success

/-- Arithmetic parsing of a core term. Its error category matches the source. -/
def linearTerm (variableOf : Name → Option Nat) (t : Term) :
    Except (LatticeLinear.Error Name) LatticeLinear.Linear :=
  LatticeLinear.linearTerm variableOf (lowerTerm t)

/-- A successful parse denotes exactly the total core integer term. -/
theorem linearTerm_correct (variableOf : Name → Option Nat) (env : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → env name = assignment index)
    (t : Term) (result : LatticeLinear.Linear)
    (success : linearTerm variableOf t = .ok result) :
    LatticeLinear.evaluate assignment result = evalTerm env t := by
  have correct := LatticeLinear.linearTerm_correct variableOf env assignment environment
    (lowerTerm t) result success
  rw [lowerTerm_evaluation] at correct
  cases h : arithmeticSupported t <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at correct
  · cases correct
  · exact (Option.some.inj correct).symm

/-- Every conditional term is rejected, including a conditional with a constant condition. -/
theorem linearTerm_rejects_ite (variableOf : Name → Option Nat)
    (p : CoreFormula.Formula) (yes no : Term) :
    linearTerm variableOf (.ite p yes no) = .error .nonlinear := by
  simp [linearTerm, lowerTerm, LatticeLinear.linearTerm]

/-- Missing variables produce the source's unknown-name error. -/
theorem linearTerm_unknownName (variableOf : Name → Option Nat) (name : Name)
    (missing : variableOf name = none) :
    linearTerm variableOf (.var name) = .error (.unknownName name) := by
  simp [linearTerm, lowerTerm, LatticeLinear.linearTerm, missing]

/-- A variable square is rejected even though the core language gives it an integer meaning. -/
theorem linearTerm_rejects_square (variableOf : Name → Option Nat) (name : Name) (index : Nat)
    (found : variableOf name = some index) :
    linearTerm variableOf (.mul (.var name) (.var name)) = .error .nonlinear := by
  simp [linearTerm, lowerTerm, LatticeLinear.linearTerm, found,
    LatticeLinear.multiplyLinear]

/-- Successful parsing excludes every conditional term from the arithmetic syntax. -/
theorem linearTerm_success_supported (variableOf : Name → Option Nat)
    (t : Term) (result : LatticeLinear.Linear)
    (success : linearTerm variableOf t = .ok result) : arithmeticSupported t = true := by
  have correct := LatticeLinear.linearTerm_correct variableOf (fun _ => 0) (fun _ => 0)
    (by intros; rfl) (lowerTerm t) result success
  rw [lowerTerm_evaluation] at correct
  cases h : arithmeticSupported t
  · simp [h] at correct
  · rfl

/-- Successful formula compilation excludes every conditional term, in every Boolean branch. -/
theorem signed_success_supported (variableOf : Name → Option Nat)
    (p : CoreFormula.Formula) (positive : Bool) (result : LatticeSigned.Checked)
    (success : signed variableOf positive p = .ok result) : formulaSupported p = true := by
  obtain ⟨value, interpreted, _⟩ :=
    LatticeFormula.signed_correct variableOf (fun _ => 0) (fun _ => 0)
      (by intros; rfl) (lowerFormula p) positive result success
  rw [lowerFormula_evaluation] at interpreted
  cases h : formulaSupported p
  · simp [h] at interpreted
  · rfl

/-- Simplification and compilation give the same score whenever both parsers succeed. -/
theorem signed_simplify_score (variableOf : Name → Option Nat) (env : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → env name = assignment index)
    (p : CoreFormula.Formula) (positive : Bool) (original simplified : LatticeSigned.Checked)
    (originalParsed : signed variableOf positive p = .ok original)
    (simplifiedParsed : signed variableOf positive (CoreFormula.simplify p) = .ok simplified) :
    LatticeSigned.score assignment simplified.terms =
      LatticeSigned.score assignment original.terms := by
  rw [signed_correct variableOf env assignment environment _ _ _ simplifiedParsed,
    signed_correct variableOf env assignment environment _ _ _ originalParsed,
    CoreFormula.eval_simplify]

/-- A formula with one allowed value, written with a constant conditional term. -/
def conditionalSingleton : CoreFormula.Formula :=
  .atom .eq (.var "x") (.ite .top (.lit 1) (.lit 2))

/-- The conditional example describes exactly one value of its sole free name. -/
theorem conditionalSingleton_semantics (env : Name → Int) :
    evalFormula env conditionalSingleton = true ↔ env "x" = 1 := by
  simp [conditionalSingleton, evalFormula, evalTerm, evalRelation]

/-- The source lattice parser rejects that finite singleton because it contains `Ite`. -/
theorem conditionalSingleton_rejected (variableOf : Name → Option Nat) :
    signed variableOf true conditionalSingleton = .error (.arithmetic .nonlinear) := by
  simp [signed, conditionalSingleton, lowerFormula, lowerTerm, LatticeFormula.signed,
    LatticeFormula.parseAtom, LatticeFormula.parseTerm, LatticeLinear.linearTerm]

end MicroCFTA.CoreLattice
