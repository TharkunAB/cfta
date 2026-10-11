import MicroCFTA.Symbolic

/-!
# Source constraint indicator compilation

`Data.CFTA.Constraint.constraintIndicators` multiplies path equality classes
and compiles the supported Boolean guard fragment to signed summands. A
residual atom preserves the unsupported guard returned by the source.
-/
namespace MicroCFTA.ConstraintIndicators
open Lattice (indicator)

/-- Signed conjunctions in the coefficient-first source representation. -/
abbrev Series (Atom : Type) := List (Int × List Atom)

/-- Interpret the complete signed expression at one term. -/
def score (test : Atom → Bool) (series : Series Atom) : Int :=
  (series.map fun (coefficient, atoms) => coefficient * indicator (atoms.all test)).sum

/-- The source's Cartesian multiplication of signed conjunctions. -/
def conjoin (left right : Series Atom) : Series Atom :=
  left.flatMap fun (coefficient, atoms) =>
    right.map fun (other, rest) => (coefficient * other, atoms ++ rest)

/-- The source's complement retains the constant summand. -/
def complement (series : Series Atom) : Series Atom :=
  (1, []) :: series.map fun (coefficient, atoms) => (-coefficient, atoms)

/-- Appending signed summands adds their values. -/
theorem score_append (test : Atom → Bool) (left right : Series Atom) :
    score test (left ++ right) = score test left + score test right := by
  simp [score]

/-- One Cartesian row has the value of its coefficient times both conjunctions. -/
theorem score_row (test : Atom → Bool) (coefficient : Int) (atoms : List Atom) (right : Series Atom) :
    score test (right.map fun (other, rest) => (coefficient * other, atoms ++ rest)) =
      coefficient * indicator (atoms.all test) * score test right := by
  induction right with
  | nil => simp [score]
  | cons entry rest ih =>
      rcases entry with ⟨other, remaining⟩
      simp only [List.map_cons, score, List.sum_cons, List.all_append, Lattice.indicator_and] at *
      rw [ih]
      grind

/-- The actual multiplication loop has exact integer-product semantics. -/
theorem score_conjoin (test : Atom → Bool) (left right : Series Atom) :
    score test (conjoin left right) = score test left * score test right := by
  induction left with
  | nil => simp [conjoin, score]
  | cons entry rest ih =>
      rcases entry with ⟨coefficient, atoms⟩
      simp only [conjoin, List.flatMap_cons, score_append] at *
      rw [score_row, ih]
      simp only [score, List.map_cons, List.sum_cons]
      grind

/-- Complement negates all prior contributions and adds exactly one. -/
theorem score_complement (test : Atom → Bool) (series : Series Atom) :
    score test (complement series) = 1 - score test series := by
  have negate : score test (series.map fun (coefficient, atoms) => (-coefficient, atoms)) = -score test series := by
    induction series with
    | nil => simp [score]
    | cons entry rest ih =>
        rcases entry with ⟨coefficient, atoms⟩
        simp only [score, List.map_cons, List.sum_cons] at *
        rw [ih]
        grind
  change 1 + score test (series.map fun (coefficient, atoms) => (-coefficient, atoms)) = 1 - score test series
  rw [negate]
  omega

/-- Constant truth has indicator one. -/
theorem score_true (test : Atom → Bool) : score test [(1, [])] = 1 := by
  simp [score, indicator]

/-- The source left fold multiplies every supplied summand expression. -/
theorem score_fold (test : Atom → Bool) (series : List (Series Atom)) (initial : Series Atom) :
    score test (series.foldl conjoin initial) = score test initial * (series.map (score test)).prod := by
  induction series generalizing initial with
  | nil => simp
  | cons first rest ih =>
      simp only [List.foldl_cons, ih, score_conjoin, List.map_cons, List.prod_cons]
      exact Int.mul_assoc _ _ _

/-- Supported guard constructors and an exact payload for every residual guard. -/
inductive Guard (Atom Residual : Type) where
  | top | bottom
  | same (atom : Atom)
  | not (guard : Guard Atom Residual)
  | and (guards : List (Guard Atom Residual))
  | or (guards : List (Guard Atom Residual))
  | residual (guard : Residual)

mutual
  /-- Compile one guard, retaining the first unsupported operand as an error. -/
  def compile : Guard Atom Residual → Except Residual (Series Atom)
    | .top => .ok [(1, [])]
    | .bottom => .ok []
    | .same atom => .ok [(1, [atom])]
    | .not guard => (compile guard).map complement
    | .and guards => (compileList guards).map (fun parts => parts.foldl conjoin [(1, [])])
    | .or guards => (compileList guards).map (fun parts => complement ((parts.map complement).foldl conjoin [(1, [])]))
    | .residual guard => .error guard

  /-- The source's left-to-right traversal of a guard list. -/
  def compileList : List (Guard Atom Residual) → Except Residual (List (Series Atom))
    | [] => .ok []
    | guard :: rest => do
        let first ← compile guard
        let remaining ← compileList rest
        pure (first :: remaining)
end

mutual
  /-- Independent Boolean guard semantics, including residual atoms. -/
  def eval (test : Atom → Bool) (residual : Residual → Bool) : Guard Atom Residual → Bool
    | .top => true
    | .bottom => false
    | .same atom => test atom
    | .not guard => !eval test residual guard
    | .and guards => all test residual guards
    | .or guards => any test residual guards
    | .residual guard => residual guard

  /-- Conjunction of the complete source guard list. -/
  def all (test : Atom → Bool) (residual : Residual → Bool) : List (Guard Atom Residual) → Bool
    | [] => true
    | guard :: rest => eval test residual guard && all test residual rest

  /-- Disjunction of the complete source guard list. -/
  def any (test : Atom → Bool) (residual : Residual → Bool) : List (Guard Atom Residual) → Bool
    | [] => false
    | guard :: rest => eval test residual guard || any test residual rest
end

/-- Complement of a Boolean indicator. -/
theorem indicator_not (value : Bool) : indicator (!value) = 1 - indicator value := by
  cases value <;> decide

/-- Correct compiled operands give the exact conjunction product. -/
theorem all_product (test : Atom → Bool) (residual : Residual → Bool)
    (guards : List (Guard Atom Residual)) (parts : List (Series Atom))
    (correct : Language.All₂ (fun guard part => score test part = indicator (eval test residual guard)) guards parts) :
    (parts.map (score test)).prod = indicator (all test residual guards) := by
  induction correct with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.prod_cons, head, ih, all, Lattice.indicator_and]

/-- Correct compiled operands give the exact De Morgan product used for disjunction. -/
theorem any_product (test : Atom → Bool) (residual : Residual → Bool)
    (guards : List (Guard Atom Residual)) (parts : List (Series Atom))
    (correct : Language.All₂ (fun guard part => score test part = indicator (eval test residual guard)) guards parts) :
    ((parts.map complement).map (score test)).prod = indicator (!any test residual guards) := by
  induction correct with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.prod_cons, score_complement, head, ih, any]
      rw [← indicator_not, ← Lattice.indicator_and]
      cases eval test residual _ <;> cases any test residual _ <;> rfl

/-- Every successful source guard compilation has the exact Boolean indicator. -/
theorem compile_correct (test : Atom → Bool) (residual : Residual → Bool)
    (guard : Guard Atom Residual) (series : Series Atom) (success : compile guard = .ok series) :
    score test series = indicator (eval test residual guard) := by
  induction guard using Guard.rec
    (motive_2 := fun guards => ∀ parts, compileList guards = .ok parts →
      Language.All₂ (fun guard part => score test part = indicator (eval test residual guard)) guards parts)
    generalizing series with
  | top => cases success; exact score_true test
  | bottom => cases success; rfl
  | same atom => cases success; simp [score, eval]
  | residual guard => cases success
  | not guard ih =>
      cases compiled : compile guard with
      | error error => simp [compile, compiled, Except.map] at success
      | ok result =>
          have same : complement result = series := by simpa [compile, compiled, Except.map] using success
          subst series
          rw [score_complement, ih result compiled]
          exact (indicator_not _).symm
  | and guards ih =>
      cases compiled : compileList guards with
      | error error => simp [compile, compiled, Except.map] at success
      | ok parts =>
          have same : parts.foldl conjoin [(1, [])] = series := by simpa [compile, compiled, Except.map] using success
          subst series
          rw [score_fold, score_true, Int.one_mul, all_product test residual guards parts (ih parts compiled)]
          rfl
  | or guards ih =>
      cases compiled : compileList guards with
      | error error => simp [compile, compiled, Except.map] at success
      | ok parts =>
          have same : complement ((parts.map complement).foldl conjoin [(1, [])]) = series :=
            by simpa [compile, compiled, Except.map] using success
          subst series
          rw [score_complement, score_fold, score_true, Int.one_mul,
            any_product test residual guards parts (ih parts compiled), indicator_not]
          simp only [eval]
          omega
  | nil => rename_i parts success; cases success; exact .nil
  | cons guard rest ih ihtail =>
      rename_i parts success
      cases first : compile guard with
      | error error => simp [compileList, first, Bind.bind, Except.bind] at success
      | ok part =>
          cases remaining : compileList rest with
          | error error => simp [compileList, first, remaining, Bind.bind, Except.bind] at success
          | ok tail =>
              have same : part :: tail = parts := by simpa [compileList, first, remaining, Bind.bind, Except.bind, Pure.pure, Except.pure] using success
              subst parts
              exact .cons (ih part first) (ihtail tail remaining)

/-- A normalized contradiction has no summand; other equalities have one. -/
def equalityIndicators : Option (List Atom) → Series Atom
  | none => []
  | some classes => [(1, classes)]

/-- The concrete equality part's Boolean meaning, including contradiction. -/
def equalityValue (test : Atom → Bool) : Option (List Atom) → Bool
  | none => false
  | some classes => classes.all test

/-- Read normalized equalities without losing an existence requirement. -/
theorem equality_correct (test : Atom → Bool) (classes : Option (List Atom)) :
    score test (equalityIndicators classes) = indicator (equalityValue test classes) := by
  cases classes <;> simp [score, equalityIndicators, equalityValue, indicator]

/-- Compile the entire transition constraint in source order. -/
def constraintIndicators (classes : Option (List Atom)) (guard : Guard Atom Residual) : Except Residual (Series Atom) :=
  (compile guard).map (conjoin (equalityIndicators classes))

/-- Every successful transition compilation is its exact Boolean indicator. -/
theorem constraint_correct (test : Atom → Bool) (residual : Residual → Bool)
    (classes : Option (List Atom)) (guard : Guard Atom Residual) (series : Series Atom)
    (success : constraintIndicators classes guard = .ok series) :
    score test series = indicator (equalityValue test classes && eval test residual guard) := by
  cases result : compile guard with
  | error error => simp [constraintIndicators, result, Except.map] at success
  | ok compiled =>
      have same : conjoin (equalityIndicators classes) compiled = series := by
        simpa [constraintIndicators, result, Except.map] using success
      subst series
      rw [score_conjoin, equality_correct, compile_correct test residual guard compiled result,
        Lattice.indicator_and]

/-- Signed intermediate coefficients still give exactly zero or one at each term. -/
theorem constraint_boolean (test : Atom → Bool) (residual : Residual → Bool)
    (classes : Option (List Atom)) (guard : Guard Atom Residual) (series : Series Atom)
    (success : constraintIndicators classes guard = .ok series) :
    score test series = 0 ∨ score test series = 1 := by
  rw [constraint_correct test residual classes guard series success]
  cases equalityValue test classes && eval test residual guard <;> simp [indicator]

/-- A required unsupported guard remains an error, even under false equalities. -/
theorem residual_error (classes : Option (List Atom)) (guard : Residual) :
    constraintIndicators classes (.residual guard) = .error guard := rfl

end MicroCFTA.ConstraintIndicators
