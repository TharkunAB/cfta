import MicroCFTA.LatticeSigned

/-!
# Integer formula compilation

This syntax is the supported integer fragment of the Fixpoint formula syntax.
Conjunction and disjunction lists use right folds with their source identities.
The parser compiles arithmetic terms, propagates polarity to the atoms, and
uses the executable signed-conjunction simplifier at each Boolean operation.
-/

namespace MicroCFTA.LatticeFormula
open LatticeLinear LatticeSigned

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- Boolean syntax over supported integer expressions. -/
inductive Formula (Name : Type) where
  | atom (relation : Relation) (left right : Expr Name)
  | top | bottom
  | conj (left right : Formula Name)
  | disj (left right : Formula Name)
  | neg (inner : Formula Name)
  | imp (premise conclusion : Formula Name)
  | iff (left right : Formula Name)
  | cast (inner : Formula Name)
  | unsupported

/-- Read an n-ary conjunction with the source's empty-list identity. -/
def all (parts : List (Formula Name)) : Formula Name := parts.foldr Formula.conj .top

/-- Read an n-ary disjunction with the source's empty-list identity. -/
def any (parts : List (Formula Name)) : Formula Name := parts.foldr Formula.disj .bottom

/-- Evaluate a formula independently of its compiled inequalities. -/
def evaluateFormula (names : Name → Int) : Formula Name → Option Bool
  | .atom relation left right => do
      pure (relationHolds relation (← evalExpr names left) (← evalExpr names right))
  | .top => some true
  | .bottom => some false
  | .conj left right => do pure ((← evaluateFormula names left) && (← evaluateFormula names right))
  | .disj left right => do pure ((← evaluateFormula names left) || (← evaluateFormula names right))
  | .neg inner => (evaluateFormula names inner).map (! ·)
  | .imp premise conclusion => do pure (!(← evaluateFormula names premise) || (← evaluateFormula names conclusion))
  | .iff left right => do pure ((← evaluateFormula names left) == (← evaluateFormula names right))
  | .cast inner => evaluateFormula names inner
  | .unsupported => none

/-- Preserve the arithmetic error, or report unsupported Boolean syntax. -/
inductive Error (Name : Type) where
  | arithmetic (error : LatticeLinear.Error Name)
  | unsupported

/-- Parse one arithmetic term and retain its derived sparse-map invariant. -/
def parseTerm (variableOf : Name → Option Nat) (expression : Expr Name) :
    Except (Error Name) { form : Linear // Valid form } :=
  match parsed : linearTerm variableOf expression with
  | .error error => .error (.arithmetic error)
  | .ok form => .ok ⟨form, linearTerm_valid variableOf expression form parsed⟩

/-- Arithmetic parsing remains exact when its representation proof is retained. -/
theorem parseTerm_correct (variableOf : Name → Option Nat) (names : Name → Int) (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → names name = assignment index)
    (expression : Expr Name) (result : { form : Linear // Valid form })
    (success : parseTerm variableOf expression = .ok result) :
    evalExpr names expression = some (evaluate assignment result.val) := by
  unfold parseTerm at success
  split at success
  · cases success
  · next form parsed =>
    cases success
    exact linearTerm_correct variableOf names assignment environment expression form parsed

/-- Parse an atom using the source's right-minus-left difference. -/
def parseAtom (variableOf : Name → Option Nat) (positive : Bool) (relation : Relation)
    (left right : Expr Name) : Except (Error Name) Checked := do
  let rightForm ← parseTerm variableOf right
  let leftForm ← parseTerm variableOf left
  .ok (LatticeSigned.atom (if positive then relation else opposite relation)
    (minus rightForm.val leftForm.val) (minus_valid _ _ rightForm.property leftForm.property))

/-- Compile Boolean connectives with the same signed products and inclusion/exclusion. -/
def signed (variableOf : Name → Option Nat) (positive : Bool) : Formula Name → Except (Error Name) Checked
  | .atom relation left right => parseAtom variableOf positive relation left right
  | .top => .ok (if positive then always else never)
  | .bottom => .ok (if positive then never else always)
  | .conj left right => do
      let lhs ← signed variableOf positive left
      let rhs ← signed variableOf positive right
      .ok (if positive then conjoin lhs rhs else disjoin lhs rhs)
  | .disj left right => do
      let lhs ← signed variableOf positive left
      let rhs ← signed variableOf positive right
      .ok (if positive then disjoin lhs rhs else conjoin lhs rhs)
  | .neg inner => signed variableOf (!positive) inner
  | .imp premise conclusion => do
      let lhs ← signed variableOf (!positive) premise
      let rhs ← signed variableOf positive conclusion
      .ok (if positive then disjoin lhs rhs else conjoin lhs rhs)
  | .iff left right => do
      let leftPositive ← signed variableOf true left
      let rightFirst ← signed variableOf positive right
      let leftNegative ← signed variableOf false left
      let rightSecond ← signed variableOf (!positive) right
      .ok (disjoin (conjoin leftPositive rightFirst) (conjoin leftNegative rightSecond))
  | .cast inner => signed variableOf positive inner
  | .unsupported => .error .unsupported

/-- A parsed atom has exactly its independent truth value in either polarity. -/
theorem parseAtom_correct (variableOf : Name → Option Nat) (names : Name → Int) (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → names name = assignment index)
    (positive : Bool) (relation : Relation) (left right : Expr Name) (result : Checked)
    (success : parseAtom variableOf positive relation left right = .ok result) :
    ∃ value, evaluateFormula names (.atom relation left right) = some value ∧
      score assignment result.terms = Lattice.indicator (value == positive) := by
  cases rightParsed : parseTerm variableOf right with
  | error error => simp [parseAtom, rightParsed] at success
  | ok rightForm =>
    cases leftParsed : parseTerm variableOf left with
    | error error => simp [parseAtom, rightParsed, leftParsed] at success
    | ok leftForm =>
      simp [parseAtom, rightParsed, leftParsed] at success
      cases success
      have rightValue := parseTerm_correct variableOf names assignment environment right rightForm rightParsed
      have leftValue := parseTerm_correct variableOf names assignment environment left leftForm leftParsed
      refine ⟨relationHolds relation (evaluate assignment leftForm.val) (evaluate assignment rightForm.val), ?_, ?_⟩
      · simp [evaluateFormula, rightValue, leftValue]
      · rw [atom_score assignment _ _ _ _ _ (evaluate_minus assignment rightForm.val leftForm.val)]
        cases positive <;> simp [opposite_correct]

/-- Successful formula compilation counts a satisfying assignment exactly once. -/
theorem signed_correct (variableOf : Name → Option Nat) (names : Name → Int) (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → names name = assignment index)
    (formula : Formula Name) (positive : Bool) (result : Checked)
    (success : signed variableOf positive formula = .ok result) :
    ∃ value, evaluateFormula names formula = some value ∧
      score assignment result.terms = Lattice.indicator (value == positive) := by
  induction formula generalizing positive result with
  | atom relation left right => exact parseAtom_correct variableOf names assignment environment positive relation left right result success
  | top =>
    simp [signed] at success
    cases success
    refine ⟨true, rfl, ?_⟩
    cases positive <;> simp [always, never, score, region, Lattice.indicator]
  | bottom =>
    simp [signed] at success
    cases success
    refine ⟨false, rfl, ?_⟩
    cases positive <;> simp [always, never, score, region, Lattice.indicator]
  | conj left right ihl ihr =>
    cases lhs : signed variableOf positive left with
    | error error => simp [signed, lhs] at success
    | ok lhsResult =>
      cases rhs : signed variableOf positive right with
      | error error => simp [signed, lhs, rhs] at success
      | ok rhsResult =>
        simp [signed, lhs, rhs] at success
        cases success
        obtain ⟨l, lv, ls⟩ := ihl positive lhsResult lhs
        obtain ⟨r, rv, rs⟩ := ihr positive rhsResult rhs
        refine ⟨l && r, by simp [evaluateFormula, lv, rv], ?_⟩
        cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, conjoin_score, disjoin_score, ls, rs]
        all_goals cases l <;> cases r <;> decide
  | disj left right ihl ihr =>
    cases lhs : signed variableOf positive left with
    | error error => simp [signed, lhs] at success
    | ok lhsResult =>
      cases rhs : signed variableOf positive right with
      | error error => simp [signed, lhs, rhs] at success
      | ok rhsResult =>
        simp [signed, lhs, rhs] at success
        cases success
        obtain ⟨l, lv, ls⟩ := ihl positive lhsResult lhs
        obtain ⟨r, rv, rs⟩ := ihr positive rhsResult rhs
        refine ⟨l || r, by simp [evaluateFormula, lv, rv], ?_⟩
        cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, conjoin_score, disjoin_score, ls, rs]
        all_goals cases l <;> cases r <;> decide
  | neg inner ih =>
    obtain ⟨value, evaluated, exactScore⟩ := ih (!positive) result success
    refine ⟨!value, by simp [evaluateFormula, evaluated], ?_⟩
    rw [exactScore]
    cases value <;> cases positive <;> rfl
  | imp premise conclusion ihp ihc =>
    cases lhs : signed variableOf (!positive) premise with
    | error error => simp [signed, lhs] at success
    | ok lhsResult =>
      cases rhs : signed variableOf positive conclusion with
      | error error => simp [signed, lhs, rhs] at success
      | ok rhsResult =>
        simp [signed, lhs, rhs] at success
        cases success
        obtain ⟨l, lv, ls⟩ := ihp (!positive) lhsResult lhs
        obtain ⟨r, rv, rs⟩ := ihc positive rhsResult rhs
        refine ⟨!l || r, by simp [evaluateFormula, lv, rv], ?_⟩
        cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte, conjoin_score, disjoin_score, ls, rs]
        all_goals cases l <;> cases r <;> decide
  | iff left right ihl ihr =>
    cases lp : signed variableOf true left with
    | error error => simp [signed, lp] at success
    | ok lpResult =>
      cases rp : signed variableOf positive right with
      | error error => simp [signed, lp, rp] at success
      | ok rpResult =>
        cases ln : signed variableOf false left with
        | error error => simp [signed, lp, rp, ln] at success
        | ok lnResult =>
          cases rn : signed variableOf (!positive) right with
          | error error => simp [signed, lp, rp, ln, rn] at success
          | ok rnResult =>
            simp [signed, lp, rp, ln, rn] at success
            cases success
            obtain ⟨l, lv, ls⟩ := ihl true lpResult lp
            obtain ⟨r, rv, rs⟩ := ihr positive rpResult rp
            obtain ⟨l', lv', ls'⟩ := ihl false lnResult ln
            obtain ⟨r', rv', rs'⟩ := ihr (!positive) rnResult rn
            have sameL : l' = l := Option.some.inj (lv'.symm.trans lv)
            have sameR : r' = r := Option.some.inj (rv'.symm.trans rv)
            subst l'
            subst r'
            refine ⟨l == r, by simp [evaluateFormula, lv, rv], ?_⟩
            rw [disjoin_score, conjoin_score, conjoin_score, ls, rs, ls', rs']
            cases positive <;> cases l <;> cases r <;> decide
  | cast inner ih => exact ih positive result success
  | unsupported => simp [signed] at success

/-- Traverse each formula before folding the source's Boolean connective. -/
def parseParts (variableOf : Name → Option Nat) (positive : Bool) :
    List (Formula Name) → Except (Error Name) (List Checked)
  | [] => .ok []
  | first :: rest => do
      let head ← signed variableOf positive first
      let tail ← parseParts variableOf positive rest
      .ok (head :: tail)

/-- The source's n-ary conjunction traversal and signed right fold. -/
def signedAll (variableOf : Name → Option Nat) (positive : Bool) (parts : List (Formula Name)) :
    Except (Error Name) Checked := do
  let parsed ← parseParts variableOf positive parts
  .ok (parsed.foldr (if positive then conjoin else disjoin) (if positive then always else never))

/-- The source's n-ary disjunction traversal and signed right fold. -/
def signedAny (variableOf : Name → Option Nat) (positive : Bool) (parts : List (Formula Name)) :
    Except (Error Name) Checked := do
  let parsed ← parseParts variableOf positive parts
  .ok (parsed.foldr (if positive then disjoin else conjoin) (if positive then never else always))

/-- Binary syntax expansion gives exactly the source's conjunction traversal and fold. -/
theorem signed_all_eq (variableOf : Name → Option Nat) (positive : Bool) (parts : List (Formula Name)) :
    signed variableOf positive (all parts) = signedAll variableOf positive parts := by
  induction parts with
  | nil => simp [all, signed, signedAll, parseParts]
  | cons first rest ih =>
    change signed variableOf positive (.conj first (all rest)) = _
    simp only [signed, ih]
    cases head : signed variableOf positive first <;>
      cases tail : parseParts variableOf positive rest <;>
      cases positive <;> simp [signedAll, parseParts, head, tail]

/-- Binary syntax expansion gives exactly the source's disjunction traversal and fold. -/
theorem signed_any_eq (variableOf : Name → Option Nat) (positive : Bool) (parts : List (Formula Name)) :
    signed variableOf positive (any parts) = signedAny variableOf positive parts := by
  induction parts with
  | nil => simp [any, signed, signedAny, parseParts]
  | cons first rest ih =>
    change signed variableOf positive (.disj first (any rest)) = _
    simp only [signed, ih]
    cases head : signed variableOf positive first <;>
      cases tail : parseParts variableOf positive rest <;>
      cases positive <;> simp [signedAny, parseParts, head, tail]

/-- A successfully compiled positive formula always has a natural zero-or-one score. -/
theorem signed_indicator (variableOf : Name → Option Nat) (names : Name → Int) (assignment : Nat → Int)
    (environment : ∀ name index, variableOf name = some index → names name = assignment index)
    (formula : Formula Name) (result : Checked) (success : signed variableOf true formula = .ok result) :
    ∃ value, evaluateFormula names formula = some value ∧
      score assignment result.terms = (if value then 1 else 0) := by
  obtain ⟨value, interpreted, counted⟩ := signed_correct variableOf names assignment environment formula true result success
  exact ⟨value, interpreted, by simpa [Lattice.indicator] using counted⟩

end MicroCFTA.LatticeFormula
