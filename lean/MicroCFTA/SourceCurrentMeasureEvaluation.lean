import MicroCFTA.FullSyntax

/-!
# Current integer evaluation of constructor measures

The evaluator supports literals, four arithmetic constructors, and choices.
Every other term is sent unchanged to the leaf callback. Boolean lists
evaluate every part before their Boolean fold. Quantifiers return none.
Successful results agree with full syntax semantics under integer primitive
laws and leaf readback. Sort checking and solver behavior stay separate.
-/
namespace MicroCFTA.SourceCurrentMeasureEvaluation
open FullSyntax

mutual
/-- Evaluate only the term constructors handled by the source measure worker. -/
def evaluateTerm (leaf : Term → Option Int) : Term → Option Int
  | .lit value => some value
  | .neg inner => (evaluateTerm leaf inner).map (- ·)
  | .add left right => do return (← evaluateTerm leaf left) + (← evaluateTerm leaf right)
  | .sub left right => do return (← evaluateTerm leaf left) - (← evaluateTerm leaf right)
  | .mul left right => do return (← evaluateTerm leaf left) * (← evaluateTerm leaf right)
  | .ite condition yes no => do
      let choice ← evaluateFormula leaf condition
      if choice then evaluateTerm leaf yes else evaluateTerm leaf no
  | other => leaf other
termination_by term => sizeOf term

/-- Evaluate supported formulas; quantified formulas have no result. -/
def evaluateFormula (leaf : Term → Option Int) : Formula → Option Bool
  | .top => some true
  | .bottom => some false
  | .and parts => evaluateAll leaf parts
  | .or parts => evaluateAny leaf parts
  | .not inner => (evaluateFormula leaf inner).map (! ·)
  | .atom relation left right => do
      return CoreFormula.evalRelation relation (← evaluateTerm leaf left) (← evaluateTerm leaf right)
  | .forall _ _ | .exists _ _ => none
termination_by formula => sizeOf formula

/-- Sequence every conjunction part, including those after a false result. -/
def evaluateAll (leaf : Term → Option Int) : List Formula → Option Bool
  | [] => some true
  | first :: rest => do return (← evaluateFormula leaf first) && (← evaluateAll leaf rest)
termination_by parts => sizeOf parts

/-- Sequence every disjunction part, including those after a true result. -/
def evaluateAny (leaf : Term → Option Int) : List Formula → Option Bool
  | [] => some false
  | first :: rest => do return (← evaluateFormula leaf first) || (← evaluateAny leaf rest)
termination_by parts => sizeOf parts
end

/-- The interpreted integer values obey the actual supported arithmetic and comparisons. -/
structure IntegerLaws (model : Interpretation Value) (integer : Int → Value) : Prop where
  literal : ∀ value, model.literal value = integer value
  neg : ∀ value, model.neg (integer value) = integer (-value)
  add : ∀ left right, model.add (integer left) (integer right) = integer (left + right)
  sub : ∀ left right, model.sub (integer left) (integer right) = integer (left - right)
  mul : ∀ left right, model.mul (integer left) (integer right) = integer (left * right)
  relation : ∀ relation left right, model.relation relation (integer left) (integer right) ↔
    CoreFormula.evalRelation relation left right = true

/-- A successful leaf lookup denotes that integer in the current full interpretation. -/
def LeafAgrees (model : Interpretation Value) (integer : Int → Value) (env : Name → Value)
    (leaf : Term → Option Int) : Prop :=
  ∀ term value, leaf term = some value → FullSyntax.evaluateTerm model env term = integer value

variable (model : Interpretation Value) (integer : Int → Value) (env : Name → Value)
variable (leaf : Term → Option Int)

mutual
/-- Successful source term evaluation has its independent full-syntax integer meaning. -/
theorem term_sound (laws : IntegerLaws model integer) (agrees : LeafAgrees model integer env leaf) (term : Term) (value : Int) (done : evaluateTerm leaf term = some value) :
    FullSyntax.evaluateTerm model env term = integer value := by
  cases term with
  | lit number =>
      simp only [evaluateTerm, Option.some.injEq] at done
      subst value
      simpa only [FullSyntax.evaluateTerm] using laws.literal number
  | neg inner =>
      cases found : evaluateTerm leaf inner with
      | none => simp [evaluateTerm, found] at done
      | some number =>
          have innerSound := term_sound laws agrees inner number found
          simp only [evaluateTerm, found, Option.map_some, Option.some.injEq] at done
          subst value
          simpa only [FullSyntax.evaluateTerm, innerSound] using laws.neg number
  | add left right | sub left right | mul left right =>
      cases first : evaluateTerm leaf left <;> cases second : evaluateTerm leaf right <;>
        simp [evaluateTerm, first, second] at done
      all_goals first | contradiction | skip
      all_goals subst value
      all_goals simp only [FullSyntax.evaluateTerm, term_sound laws agrees left _ first, term_sound laws agrees right _ second]
      all_goals first | exact laws.add _ _ | exact laws.sub _ _ | exact laws.mul _ _
  | ite condition yes no =>
      cases tested : evaluateFormula leaf condition with
      | none => simp [evaluateTerm, tested] at done
      | some choice =>
          have conditionSound := formula_sound laws agrees condition choice tested
          cases choice with
          | false =>
              have failed : ¬Holds model env condition := by simpa using conditionSound
              simp [evaluateTerm, tested] at done
              simpa only [FullSyntax.evaluateTerm, failed, ite_false] using term_sound laws agrees no value done
          | true =>
              have holds : Holds model env condition := conditionSound.mpr rfl
              simp [evaluateTerm, tested] at done
              simpa only [FullSyntax.evaluateTerm, holds, ite_true] using term_sound laws agrees yes value done
  | var | app | div | mod | cast => exact agrees _ _ (by simpa only [evaluateTerm] using done)
termination_by sizeOf term

/-- Successful source Boolean evaluation agrees with full classical truth. -/
theorem formula_sound (laws : IntegerLaws model integer) (agrees : LeafAgrees model integer env leaf) (formula : Formula) (value : Bool) (done : evaluateFormula leaf formula = some value) :
    Holds model env formula ↔ value = true := by
  cases formula with
  | top => simp only [evaluateFormula, Option.some.injEq] at done; subst value; simp [Holds]
  | bottom => simp only [evaluateFormula, Option.some.injEq] at done; subst value; simp [Holds]
  | and parts => simpa only [Holds] using all_sound laws agrees parts value (by simpa only [evaluateFormula] using done)
  | or parts => simpa only [Holds] using any_sound laws agrees parts value (by simpa only [evaluateFormula] using done)
  | not inner =>
      cases found : evaluateFormula leaf inner with
      | none => simp [evaluateFormula, found] at done
      | some choice =>
          have innerSound := formula_sound laws agrees inner choice found
          simp only [evaluateFormula, found, Option.map_some, Option.some.injEq] at done
          subst value
          cases choice <;> simp_all [Holds]
  | atom relation left right =>
      cases first : evaluateTerm leaf left <;> cases second : evaluateTerm leaf right <;>
        simp [evaluateFormula, first, second] at done
      all_goals first | contradiction | skip
      subst value
      simp only [Holds, term_sound laws agrees left _ first, term_sound laws agrees right _ second, laws.relation]
  | «forall» | «exists» => simp [evaluateFormula] at done
termination_by sizeOf formula

/-- Defined conjunction folds retain all parts and their independent truth. -/
theorem all_sound (laws : IntegerLaws model integer) (agrees : LeafAgrees model integer env leaf) (parts : List Formula) (value : Bool) (done : evaluateAll leaf parts = some value) :
    holdsAll model env parts ↔ value = true := by
  cases parts with
  | nil => simp only [evaluateAll, Option.some.injEq] at done; subst value; simp [holdsAll]
  | cons first rest =>
      cases head : evaluateFormula leaf first <;> cases tail : evaluateAll leaf rest <;>
        simp [evaluateAll, head, tail] at done
      all_goals first | contradiction | skip
      subst value
      simp only [holdsAll, formula_sound laws agrees first _ head, all_sound laws agrees rest _ tail, Bool.and_eq_true]
termination_by sizeOf parts

/-- Defined disjunction folds retain all parts and their independent truth. -/
theorem any_sound (laws : IntegerLaws model integer) (agrees : LeafAgrees model integer env leaf) (parts : List Formula) (value : Bool) (done : evaluateAny leaf parts = some value) :
    holdsAny model env parts ↔ value = true := by
  cases parts with
  | nil => simp only [evaluateAny, Option.some.injEq] at done; subst value; simp [holdsAny]
  | cons first rest =>
      cases head : evaluateFormula leaf first <;> cases tail : evaluateAny leaf rest <;>
        simp [evaluateAny, head, tail] at done
      all_goals first | contradiction | skip
      subst value
      simp only [holdsAny, formula_sound laws agrees first _ head, any_sound laws agrees rest _ tail, Bool.or_eq_true]
termination_by sizeOf parts
end

/-- The literal-only callback satisfies leaf readback without an additional premise. -/
theorem none_agrees : LeafAgrees model integer env (fun _ => none) := by
  intro term value impossible
  cases impossible

/-- The existing mathematical integer interpretation satisfies all supported primitive laws. -/
theorem integer_laws : IntegerLaws FullSyntax.integerModel id := by
  constructor <;> intros <;> rfl

/-- The source expression instance folds the negation of a literal immediately. -/
def negateTerm : Term → Term
  | .lit value => .lit (-value)
  | term => .neg term

/-- Integer and expression choices agree whenever the condition and selected branch evaluate. -/
theorem ite_exact (leaf : Term → Option Int) (condition : Formula) (yes no : Term) (choice : Bool)
    (tested : evaluateFormula leaf condition = some choice) :
    evaluateTerm leaf (.ite condition yes no) = if choice then evaluateTerm leaf yes else evaluateTerm leaf no := by
  simp [evaluateTerm, tested]

/-- Smart literal negation retains the same evaluated integer. -/
theorem negate_exact (leaf : Term → Option Int) (term : Term) (value : Int)
    (done : evaluateTerm leaf term = some value) : evaluateTerm leaf (negateTerm term) = some (-value) := by
  cases term with
  | lit number =>
      simp only [evaluateTerm, Option.some.injEq] at done
      subst value
      simp only [negateTerm, evaluateTerm]
  | var | app | neg | add | sub | mul | div | mod | ite | cast =>
      change evaluateTerm leaf (.neg _) = some (-value)
      rw [evaluateTerm, done]
      rfl

/-- The source smaller expression uses the non-strict comparison. -/
def smaller (left right : Term) : Term := .ite (.atom .le left right) left right

/-- The source larger expression uses the reversed non-strict comparison. -/
def larger (left right : Term) : Term := .ite (.atom .ge left right) left right

/-- The expression Num instance chooses its original term at zero. -/
def absolute (term : Term) : Term := .ite (.atom .ge term (.lit 0)) term (negateTerm term)

/-- The expression Num instance distinguishes positive, zero, and negative integers in source order. -/
def signum (term : Term) : Term :=
  .ite (.atom .gt term (.lit 0)) (.lit 1) (.ite (.atom .eq term (.lit 0)) (.lit 0) (.lit (-1)))

/-- Evaluated symbolic smaller is mathematical integer minimum. -/
theorem smaller_exact (leaf : Term → Option Int) (left right : Term) (first second : Int)
    (leftDone : evaluateTerm leaf left = some first) (rightDone : evaluateTerm leaf right = some second) :
    evaluateTerm leaf (smaller left right) = some (min first second) := by
  by_cases order : first ≤ second <;>
    simp [smaller, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, leftDone, rightDone, order, Int.min_def]

/-- Evaluated symbolic larger is mathematical integer maximum. -/
theorem larger_exact (leaf : Term → Option Int) (left right : Term) (first second : Int)
    (leftDone : evaluateTerm leaf left = some first) (rightDone : evaluateTerm leaf right = some second) :
    evaluateTerm leaf (larger left right) = some (max first second) := by
  by_cases order : second ≤ first <;>
    simp [larger, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, leftDone, rightDone, order, Int.max_def] <;> omega

/-- Evaluated symbolic absolute value agrees with the integer magnitude. -/
theorem absolute_exact (leaf : Term → Option Int) (term : Term) (value : Int)
    (done : evaluateTerm leaf term = some value) : evaluateTerm leaf (absolute term) = some (Int.ofNat value.natAbs) := by
  have negative := negate_exact leaf term value done
  by_cases nonnegative : 0 ≤ value
  · simp [absolute, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, done, nonnegative,
      Int.natAbs_of_nonneg nonnegative]
  · have nonpositive : value ≤ 0 := by omega
    simp [absolute, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, done, negative, nonnegative,
      Int.ofNat_natAbs_of_nonpos nonpositive]

/-- Evaluated symbolic signum agrees with mathematical integer sign. -/
theorem signum_exact (leaf : Term → Option Int) (term : Term) (value : Int)
    (done : evaluateTerm leaf term = some value) : evaluateTerm leaf (signum term) = some value.sign := by
  by_cases positive : 0 < value
  · simp [signum, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, done, positive, Int.sign_eq_one_of_pos positive]
  · by_cases zero : value = 0
    · subst value; simp [signum, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, done]
    · have negative : value < 0 := by omega
      simp [signum, evaluateTerm, evaluateFormula, CoreFormula.evalRelation, done, positive, zero, Int.sign_eq_neg_one_of_neg negative]

end MicroCFTA.SourceCurrentMeasureEvaluation
