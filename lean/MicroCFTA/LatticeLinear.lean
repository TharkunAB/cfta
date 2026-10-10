import MicroCFTA.LatticePolynomial
import MicroCFTA.Sparse

/-!
# Integer linear forms and supported expression parsing

The operations follow `Refinement/Lattice.hs`: sparse coefficient addition,
zero removal, scalar multiplication, partial substitution and `linearTerm`.
The expression syntax records the supported integer fragment. Translation
from Liquid Fixpoint's typed syntax remains an explicit boundary.
-/

namespace MicroCFTA.LatticeLinear
open Lean.Grind

attribute [local simp] Except.map Except.bind Except.pure

@[local simp] theorem except_bind_ok (value : α) (next : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= next) = next value := rfl

@[local simp] theorem except_bind_error (error : ε) (next : α → Except ε β) :
    ((Except.error error : Except ε α) >>= next) = .error error := rfl

@[local simp] theorem except_map_ok (map : α → β) (value : α) :
    map <$> (Except.ok value : Except ε α) = .ok (map value) := rfl

@[local simp] theorem except_map_error (map : α → β) (error : ε) :
    map <$> (Except.error error : Except ε α) = .error error := rfl

abbrev Linear := LatticePolynomial.Linear

/-- Evaluate the variable part of an integer linear form. -/
def evalCoefficients (assignment : Nat → Int) : List (Nat × Int) → Int
  | [] => 0
  | (index, coefficient) :: rest => coefficient * assignment index + evalCoefficients assignment rest

/-- Include the integer constant offset. -/
def evaluate (assignment : Nat → Int) (linear : Linear) : Int :=
  linear.offset + evalCoefficients assignment linear.coefficients

/-- Remove zero coefficients as the IntMap operations do. -/
def removeZeros (coefficients : List (Nat × Int)) : List (Nat × Int) :=
  coefficients.filter (fun entry => entry.2 != 0)

/-- A constant has no variable coefficients. -/
def constant (value : Int) : Linear := ⟨[], value⟩

/-- Add sparse coefficients and offsets, then remove zero coefficients. -/
def plus (left right : Linear) : Linear :=
  ⟨removeZeros (Sparse.addSparse left.coefficients right.coefficients), left.offset + right.offset⟩

/-- Multiply every coefficient and the offset by an integer constant. -/
def scale (factor : Int) (linear : Linear) : Linear :=
  if factor = 0 then constant 0
  else ⟨linear.coefficients.map (fun (index, coefficient) => (index, factor * coefficient)),
    factor * linear.offset⟩

/-- Subtract by adding a negated form. -/
def minus (left right : Linear) : Linear := plus left (scale (-1) right)

/-- Removing zero coefficients preserves the integer value. -/
theorem eval_removeZeros (assignment : Nat → Int) (coefficients : List (Nat × Int)) :
    evalCoefficients assignment (removeZeros coefficients) = evalCoefficients assignment coefficients := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨index, coefficient⟩
    by_cases zero : coefficient = 0 <;> simp_all [removeZeros, evalCoefficients]

/-- Sparse coefficient merging adds the two variable-part values. -/
theorem eval_addSparse (assignment : Nat → Int) (left right : List (Nat × Int)) :
    evalCoefficients assignment (Sparse.addSparse left right) =
      evalCoefficients assignment left + evalCoefficients assignment right := by
  fun_induction Sparse.addSparse left right with
  | case1 right => simp [evalCoefficients]
  | case2 head tail => simp [evalCoefficients]
  | case3 ls lv left rs rv right h ih => simp only [evalCoefficients, ih]; grind
  | case4 ls lv left rs rv right h h' ih => simp only [evalCoefficients, ih]; grind
  | case5 ls lv left rs rv right h h' ih =>
    have same : ls = rs := by omega
    subst rs
    simp only [evalCoefficients, ih]
    grind

/-- Constant construction has its declared value. -/
theorem evaluate_constant (assignment : Nat → Int) (value : Int) : evaluate assignment (constant value) = value := by
  simp [evaluate, constant, evalCoefficients]

/-- Linear addition preserves exact integer arithmetic. -/
theorem evaluate_plus (assignment : Nat → Int) (left right : Linear) :
    evaluate assignment (plus left right) = evaluate assignment left + evaluate assignment right := by
  simp only [evaluate, plus, eval_removeZeros, eval_addSparse]
  omega

/-- Scaling the coefficient list scales its value. -/
theorem eval_scaleCoefficients (assignment : Nat → Int) (factor : Int) (coefficients : List (Nat × Int)) :
    evalCoefficients assignment (coefficients.map (fun (index, coefficient) => (index, factor * coefficient))) =
      factor * evalCoefficients assignment coefficients := by
  induction coefficients with
  | nil => simp [evalCoefficients]
  | cons entry rest ih =>
    rcases entry with ⟨index, coefficient⟩
    simp only [List.map_cons, evalCoefficients, ih]
    grind

/-- Scalar multiplication preserves exact integer arithmetic, including a zero factor. -/
theorem evaluate_scale (assignment : Nat → Int) (factor : Int) (linear : Linear) :
    evaluate assignment (scale factor linear) = factor * evaluate assignment linear := by
  by_cases zero : factor = 0
  · simp [scale, zero, evaluate_constant]
  · simp only [scale, zero, ↓reduceIte, evaluate, eval_scaleCoefficients]
    grind

/-- Subtraction preserves exact integer arithmetic. -/
theorem evaluate_minus (assignment : Nat → Int) (left right : Linear) :
    evaluate assignment (minus left right) = evaluate assignment left - evaluate assignment right := by
  rw [minus, evaluate_plus, evaluate_scale]
  omega

/-- Each present variable receives its specified substitution value. -/
def override (values : Nat → Option Int) (assignment : Nat → Int) : Nat → Int :=
  fun index => (values index).getD (assignment index)

/-- The offset added by assigned coefficients. -/
def assignedOffset (values : Nat → Option Int) : List (Nat × Int) → Int
  | [] => 0
  | (index, coefficient) :: rest =>
      (match values index with | none => 0 | some value => coefficient * value) + assignedOffset values rest

/-- Delete assigned variables and move their contributions to the offset. -/
def substitute (values : Nat → Option Int) (linear : Linear) : Linear :=
  ⟨linear.coefficients.filter (fun entry => (values entry.1).isNone),
    linear.offset + assignedOffset values linear.coefficients⟩

/-- Assigned and remaining coefficients partition the complete linear value. -/
theorem substitute_coefficients (values : Nat → Option Int) (assignment : Nat → Int)
    (coefficients : List (Nat × Int)) :
    assignedOffset values coefficients +
      evalCoefficients assignment (coefficients.filter (fun entry => (values entry.1).isNone)) =
      evalCoefficients (override values assignment) coefficients := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨index, coefficient⟩
    cases found : values index <;>
      simp only [assignedOffset, found, List.filter_cons, evalCoefficients, override,
        Option.getD_none, Option.getD_some, Option.isNone_none, Option.isNone_some,
        Bool.false_eq_true, ↓reduceIte] <;> grind

/-- Partial substitution agrees with direct evaluation at the overridden assignment. -/
theorem evaluate_substitute (values : Nat → Option Int) (assignment : Nat → Int) (linear : Linear) :
    evaluate assignment (substitute values linear) = evaluate (override values assignment) linear := by
  simp only [evaluate, substitute]
  rw [Int.add_assoc, substitute_coefficients]

/-- Integer evaluation embeds exactly into the rational polynomial interpretation. -/
theorem coefficient_rat_bridge (assignment : Nat → Int) (coefficients : List (Nat × Int)) :
    (evalCoefficients assignment coefficients : Rat) =
      LatticePolynomial.evaluateLinearTerms (fun index => (assignment index : Rat)) coefficients := by
  induction coefficients with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨index, coefficient⟩
    simp [evalCoefficients, LatticePolynomial.evaluateLinearTerms, Rat.intCast_add, Rat.intCast_mul, ih]

theorem evaluate_rat_bridge (assignment : Nat → Int) (linear : Linear) :
    (evaluate assignment linear : Rat) = LatticePolynomial.evaluateLinear (fun index => (assignment index : Rat)) linear := by
  simp [evaluate, LatticePolynomial.evaluateLinear, Rat.intCast_add, coefficient_rat_bridge]

/-- The integer expression forms accepted by the linear parser. -/
inductive Expr (Name : Type) where
  | integer (value : Int)
  | name (identifier : Name)
  | neg (inner : Expr Name)
  | cast (inner : Expr Name)
  | add (left right : Expr Name)
  | sub (left right : Expr Name)
  | mul (left right : Expr Name)
  | unsupported

/-- Name lookup failure or an expression outside the linear fragment. -/
inductive Error (Name : Type) where
  | unknownName (identifier : Name)
  | nonlinear

/-- Interpret the integer syntax independently of linear-form construction. -/
def evalExpr (assignment : Name → Int) : Expr Name → Option Int
  | .integer value => some value
  | .name identifier => some (assignment identifier)
  | .neg inner => (evalExpr assignment inner).map (- ·)
  | .cast inner => evalExpr assignment inner
  | .add left right => do pure ((← evalExpr assignment left) + (← evalExpr assignment right))
  | .sub left right => do pure ((← evalExpr assignment left) - (← evalExpr assignment right))
  | .mul left right => do pure ((← evalExpr assignment left) * (← evalExpr assignment right))
  | .unsupported => none

/-- Multiply only when at least one parsed operand has no variable coefficients. -/
def multiplyLinear (left right : Linear) : Except (Error Name) Linear :=
  if left.coefficients.isEmpty then .ok (scale left.offset right)
  else if right.coefficients.isEmpty then .ok (scale right.offset left)
  else .error .nonlinear

/-- Parse supported syntax with the same constant-product check as `linearTerm`. -/
def linearTerm (variableOf : Name → Option Nat) : Expr Name → Except (Error Name) Linear
  | .integer value => .ok (constant value)
  | .name identifier => match variableOf identifier with
      | none => .error (.unknownName identifier)
      | some index => .ok ⟨[(index, 1)], 0⟩
  | .neg inner => (linearTerm variableOf inner).map (scale (-1))
  | .cast inner => linearTerm variableOf inner
  | .add left right => do pure (plus (← linearTerm variableOf left) (← linearTerm variableOf right))
  | .sub left right => do pure (minus (← linearTerm variableOf left) (← linearTerm variableOf right))
  | .mul left right => do multiplyLinear (← linearTerm variableOf left) (← linearTerm variableOf right)
  | .unsupported => .error .nonlinear

/-- A successful product of parsed forms has the exact product value. -/
theorem multiplyLinear_correct (assignment : Nat → Int) (left right result : Linear)
    (success : multiplyLinear (Name := Name) left right = .ok result) :
    evaluate assignment result = evaluate assignment left * evaluate assignment right := by
  unfold multiplyLinear at success
  split at success
  · next empty =>
    have coefficients : left.coefficients = [] := List.isEmpty_iff.mp empty
    cases success
    rw [evaluate_scale]
    simp [evaluate, coefficients, evalCoefficients]
  · split at success
    · next empty =>
      have coefficients : right.coefficients = [] := List.isEmpty_iff.mp empty
      cases success
      rw [evaluate_scale]
      simp [evaluate, coefficients, evalCoefficients, Int.mul_comm]
    · cases success

/-- Successful linear parsing agrees with independent integer expression evaluation. -/
theorem linearTerm_correct (variableOf : Name → Option Nat) (names : Name → Int)
    (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → names name = assignment index)
    (expression : Expr Name) (result : Linear) (success : linearTerm variableOf expression = .ok result) :
    evalExpr names expression = some (evaluate assignment result) := by
  induction expression generalizing result with
  | integer value =>
    simp [linearTerm] at success
    subst result
    simp [evalExpr, evaluate_constant]
  | name identifier =>
    cases found : variableOf identifier with
    | none => simp [linearTerm, found] at success
    | some index =>
      simp [linearTerm, found] at success
      subst result
      simp [evalExpr, evaluate, evalCoefficients, environment identifier index found]
  | neg inner ih =>
    cases parsed : linearTerm variableOf inner with
    | error why => simp [linearTerm, parsed] at success
    | ok form =>
      simp [linearTerm, parsed] at success
      subst result
      simp [evalExpr, ih form parsed, evaluate_scale]
  | cast inner ih => exact ih result success
  | add left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        simp [linearTerm, parsedLeft, parsedRight] at success
        subst result
        simp [evalExpr, ihl leftForm parsedLeft, ihr rightForm parsedRight, evaluate_plus]
  | sub left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        simp [linearTerm, parsedLeft, parsedRight] at success
        subst result
        simp [evalExpr, ihl leftForm parsedLeft, ihr rightForm parsedRight, evaluate_minus]
  | mul left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        have multiplied : multiplyLinear (Name := Name) leftForm rightForm = .ok result := by
          simpa [linearTerm, parsedLeft, parsedRight] using success
        simp [evalExpr, ihl leftForm parsedLeft, ihr rightForm parsedRight,
          multiplyLinear_correct assignment leftForm rightForm result multiplied]
  | unsupported => simp [linearTerm] at success

/-- Sparse linear forms have increasing variable indices and nonzero coefficients. -/
def Valid (linear : Linear) : Prop :=
  Sparse.Ordered linear.coefficients ∧ ∀ entry ∈ linear.coefficients, entry.2 ≠ 0

theorem constant_valid (value : Int) : Valid (constant value) := by
  simp [Valid, constant, Sparse.Ordered]

/-- Sparse addition preserves the map invariant and removes canceled coefficients. -/
theorem plus_valid (left right : Linear) (hl : Valid left) (hr : Valid right) : Valid (plus left right) := by
  constructor
  · exact (Sparse.addSparse_ordered left.coefficients right.coefficients hl.1 hr.1).filter _
  · intro entry member
    have nonzero := (List.mem_filter.mp member).2
    simpa using nonzero

/-- Multiplication by a nonzero integer keeps every nonzero coefficient nonzero. -/
theorem scale_valid (factor : Int) (linear : Linear) (valid : Valid linear) : Valid (scale factor linear) := by
  by_cases zero : factor = 0
  · simpa [scale, zero] using constant_valid 0
  · simp only [scale, zero, ↓reduceIte, Valid]
    constructor
    · simpa [Sparse.Ordered, List.pairwise_map] using valid.1
    · intro entry member
      obtain ⟨original, present, same⟩ := List.mem_map.mp member
      subst entry
      exact Int.mul_ne_zero zero (valid.2 original present)

theorem minus_valid (left right : Linear) (hl : Valid left) (hr : Valid right) : Valid (minus left right) :=
  plus_valid left (scale (-1) right) hl (scale_valid (-1) right hr)

/-- Substitution preserves variable ordering and nonzero stored coefficients. -/
theorem substitute_valid (values : Nat → Option Int) (linear : Linear) (valid : Valid linear) :
    Valid (substitute values linear) :=
  ⟨valid.1.filter _, fun entry member => valid.2 entry (List.mem_filter.mp member).1⟩

/-- Every successfully parsed form has canonical sparse coefficient metadata. -/
theorem linearTerm_valid (variableOf : Name → Option Nat) (expression : Expr Name) (result : Linear)
    (success : linearTerm variableOf expression = .ok result) : Valid result := by
  induction expression generalizing result with
  | integer value =>
    simp [linearTerm] at success
    subst result
    exact constant_valid value
  | name identifier =>
    cases found : variableOf identifier with
    | none => simp [linearTerm, found] at success
    | some index =>
      simp [linearTerm, found] at success
      subst result
      simp [Valid, Sparse.Ordered]
  | neg inner ih =>
    cases parsed : linearTerm variableOf inner with
    | error why => simp [linearTerm, parsed] at success
    | ok form =>
      simp [linearTerm, parsed] at success
      subst result
      exact scale_valid (-1) form (ih form parsed)
  | cast inner ih => exact ih result success
  | add left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        simp [linearTerm, parsedLeft, parsedRight] at success
        subst result
        exact plus_valid _ _ (ihl _ parsedLeft) (ihr _ parsedRight)
  | sub left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        simp [linearTerm, parsedLeft, parsedRight] at success
        subst result
        exact minus_valid _ _ (ihl _ parsedLeft) (ihr _ parsedRight)
  | mul left right ihl ihr =>
    cases parsedLeft : linearTerm variableOf left with
    | error why => simp [linearTerm, parsedLeft] at success
    | ok leftForm =>
      cases parsedRight : linearTerm variableOf right with
      | error why => simp [linearTerm, parsedLeft, parsedRight] at success
      | ok rightForm =>
        have multiplied : multiplyLinear (Name := Name) leftForm rightForm = .ok result := by
          simpa [linearTerm, parsedLeft, parsedRight] using success
        unfold multiplyLinear at multiplied
        split at multiplied
        · cases multiplied; exact scale_valid _ _ (ihr _ parsedRight)
        · split at multiplied
          · cases multiplied; exact scale_valid _ _ (ihl _ parsedLeft)
          · cases multiplied
  | unsupported => simp [linearTerm] at success

end MicroCFTA.LatticeLinear
