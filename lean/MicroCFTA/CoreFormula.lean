import Std

/-!
# Integer formulas from `Data.CFTA.Formula`

The syntax is the integer fragment from `55fe503`. `FullSyntax` models the
later sorted extension and proves that successful lattice parses remain in
this fragment. Integer arithmetic has the same unbounded domain as Haskell
`Integer`. An environment assigns an integer to each name.

The substitution model retains the source order of replacements and removes
identity replacements before lookup. It does not substitute inside replacement
terms. The simplifier model below preserves the source branch order.
-/

namespace MicroCFTA.CoreFormula

/-- A name denotes one integer. -/
abbrev Name := String

/-- The six integer relations, in source constructor order. -/
inductive Relation where
  | eq | ne | gt | ge | lt | le
  deriving DecidableEq, Repr

mutual
/-- The integer term fragment used by the automata. -/
inductive Term where
  | lit (value : Int)
  | var (name : Name)
  | neg (inner : Term)
  | add (left right : Term)
  | sub (left right : Term)
  | mul (left right : Term)
  | ite (condition : Formula) (yes no : Term)
  deriving Repr

/-- Quantifier-free formulas over the integer term fragment. -/
inductive Formula where
  | top
  | and (parts : List Formula)
  | bottom
  | or (parts : List Formula)
  | not (inner : Formula)
  | atom (relation : Relation) (left right : Term)
  deriving Repr
end

mutual
/-- Structural term equality. Formula conditions in `ite` are compared too. -/
def termEq : Term → Term → Bool
  | .lit a, .lit b => a == b
  | .var a, .var b => a == b
  | .neg a, .neg b => termEq a b
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d =>
      termEq a c && termEq b d
  | .ite p a b, .ite q c d => formulaEq p q && termEq a c && termEq b d
  | _, _ => false
termination_by a _ => sizeOf a

/-- Structural formula equality. Part order and repetitions are significant. -/
def formulaEq : Formula → Formula → Bool
  | .top, .top | .bottom, .bottom => true
  | .and ps, .and qs | .or ps, .or qs => formulasEq ps qs
  | .not p, .not q => formulaEq p q
  | .atom r a b, .atom s c d => r == s && termEq a c && termEq b d
  | _, _ => false
termination_by p _ => sizeOf p

/-- Structural equality for lists of formulas. -/
def formulasEq : List Formula → List Formula → Bool
  | [], [] => true
  | p :: ps, q :: qs => formulaEq p q && formulasEq ps qs
  | _, _ => false
termination_by ps _ => sizeOf ps
end

mutual
/-- Structural equality recognizes exactly equal terms. -/
theorem termEq_iff (a b : Term) : termEq a b = true ↔ a = b := by
  cases a with
  | lit n => cases b <;> simp [termEq]
  | var n => cases b <;> simp [termEq]
  | neg t => cases b <;> simp [termEq, termEq_iff t]
  | add t u => cases b <;> simp [termEq, termEq_iff t, termEq_iff u]
  | sub t u => cases b <;> simp [termEq, termEq_iff t, termEq_iff u]
  | mul t u => cases b <;> simp [termEq, termEq_iff t, termEq_iff u]
  | ite p t u => cases b <;>
      simp [termEq, formulaEq_iff p, termEq_iff t, termEq_iff u, and_assoc]
termination_by sizeOf a

/-- Structural equality recognizes exactly equal formulas. -/
theorem formulaEq_iff (p q : Formula) : formulaEq p q = true ↔ p = q := by
  cases p with
  | top => cases q <;> simp [formulaEq]
  | bottom => cases q <;> simp [formulaEq]
  | and ps => cases q <;> simp [formulaEq, formulasEq_iff ps]
  | or ps => cases q <;> simp [formulaEq, formulasEq_iff ps]
  | not p => cases q <;> simp [formulaEq, formulaEq_iff p]
  | atom r t u => cases q <;>
      simp [formulaEq, termEq_iff t, termEq_iff u, and_assoc]
termination_by sizeOf p

/-- Structural equality recognizes exactly equal lists of formulas. -/
theorem formulasEq_iff (ps qs : List Formula) : formulasEq ps qs = true ↔ ps = qs := by
  cases ps with
  | nil => cases qs <;> simp [formulasEq]
  | cons p ps => cases qs <;> simp [formulasEq, formulaEq_iff p, formulasEq_iff ps]
termination_by sizeOf ps
end

instance : BEq Term := ⟨termEq⟩
instance : LawfulBEq Term where
  eq_of_beq := (termEq_iff _ _).mp
  rfl := (termEq_iff _ _).mpr rfl

instance : BEq Formula := ⟨formulaEq⟩
instance : LawfulBEq Formula where
  eq_of_beq := (formulaEq_iff _ _).mp
  rfl := (formulaEq_iff _ _).mpr rfl

instance : DecidableEq Term := instDecidableEqOfLawfulBEq
instance : DecidableEq Formula := instDecidableEqOfLawfulBEq

/-- Evaluate an integer comparison. -/
def evalRelation : Relation → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)

mutual
/-- Evaluate a term under an assignment to all names. -/
def evalTerm (env : Name → Int) : Term → Int
  | .lit x => x
  | .var x => env x
  | .neg x => -evalTerm env x
  | .add x y => evalTerm env x + evalTerm env y
  | .sub x y => evalTerm env x - evalTerm env y
  | .mul x y => evalTerm env x * evalTerm env y
  | .ite p x y => if evalFormula env p then evalTerm env x else evalTerm env y
termination_by t => sizeOf t

/-- Evaluate a formula, including empty conjunctions and disjunctions. -/
def evalFormula (env : Name → Int) : Formula → Bool
  | .top => true
  | .and ps => evalAll env ps
  | .bottom => false
  | .or ps => evalAny env ps
  | .not p => !(evalFormula env p)
  | .atom r x y => evalRelation r (evalTerm env x) (evalTerm env y)
termination_by p => sizeOf p

/-- Evaluate all parts of a conjunction. -/
def evalAll (env : Name → Int) : List Formula → Bool
  | [] => true
  | p :: ps => evalFormula env p && evalAll env ps
termination_by ps => sizeOf ps

/-- Evaluate all parts of a disjunction. -/
def evalAny (env : Name → Int) : List Formula → Bool
  | [] => false
  | p :: ps => evalFormula env p || evalAny env ps
termination_by ps => sizeOf ps
end

/-- Remove identity replacements before the first-match lookup. -/
def active (replacements : List (Name × Term)) : List (Name × Term) :=
  replacements.filter fun (name, term) => !(term == .var name)

/-- Find the first replacement, without evaluating later entries. -/
def lookup (name : Name) : List (Name × Term) → Option Term
  | [] => none
  | (key, term) :: rest => if name = key then some term else lookup name rest

/-- Replace one variable. Replacement terms do not receive substitution. -/
def replacement (replacements : List (Name × Term)) (name : Name) : Term :=
  (lookup name (active replacements)).getD (.var name)

mutual
/-- Simultaneous substitution in a term. -/
def substituteTerm (replacements : List (Name × Term)) : Term → Term
  | .lit n => .lit n
  | .var name => replacement replacements name
  | .neg t => .neg (substituteTerm replacements t)
  | .add a b => .add (substituteTerm replacements a) (substituteTerm replacements b)
  | .sub a b => .sub (substituteTerm replacements a) (substituteTerm replacements b)
  | .mul a b => .mul (substituteTerm replacements a) (substituteTerm replacements b)
  | .ite p a b => .ite (substitute replacements p)
      (substituteTerm replacements a) (substituteTerm replacements b)
termination_by t => sizeOf t

/-- Simultaneous substitution in a formula, as in `substitute`. -/
def substitute (replacements : List (Name × Term)) : Formula → Formula
  | .top => .top
  | .bottom => .bottom
  | .and ps => .and (substituteParts replacements ps)
  | .or ps => .or (substituteParts replacements ps)
  | .not p => .not (substitute replacements p)
  | .atom r a b => .atom r (substituteTerm replacements a) (substituteTerm replacements b)
termination_by p => sizeOf p

/-- Apply one simultaneous substitution to every part. -/
def substituteParts (replacements : List (Name × Term)) : List Formula → List Formula
  | [] => []
  | p :: ps => substitute replacements p :: substituteParts replacements ps
termination_by ps => sizeOf ps
end

/-- The assignment induced by simultaneous substitution. -/
def substitutedEnv (env : Name → Int) (replacements : List (Name × Term)) : Name → Int :=
  fun name => evalTerm env (replacement replacements name)

mutual
/-- Term substitution agrees with the induced assignment, including `ite`. -/
theorem eval_substituteTerm (env : Name → Int) (rs : List (Name × Term))
    (t : Term) : evalTerm env (substituteTerm rs t) =
      evalTerm (substitutedEnv env rs) t := by
  cases t with
  | lit n => simp [substituteTerm, evalTerm]
  | var n => simp [substituteTerm, evalTerm, substitutedEnv]
  | neg t => simp [substituteTerm, evalTerm, eval_substituteTerm env rs t]
  | add t u => simp [substituteTerm, evalTerm,
      eval_substituteTerm env rs t, eval_substituteTerm env rs u]
  | sub t u => simp [substituteTerm, evalTerm,
      eval_substituteTerm env rs t, eval_substituteTerm env rs u]
  | mul t u => simp [substituteTerm, evalTerm,
      eval_substituteTerm env rs t, eval_substituteTerm env rs u]
  | ite p t u => simp [substituteTerm, evalTerm, eval_substitute env rs p,
      eval_substituteTerm env rs t, eval_substituteTerm env rs u]
termination_by sizeOf t

/-- Formula substitution preserves its exact meaning under the induced assignment. -/
theorem eval_substitute (env : Name → Int) (rs : List (Name × Term))
    (p : Formula) : evalFormula env (substitute rs p) =
      evalFormula (substitutedEnv env rs) p := by
  cases p with
  | top => simp [substitute, evalFormula]
  | bottom => simp [substitute, evalFormula]
  | and ps => simp [substitute, evalFormula, eval_substituteAll env rs ps]
  | or ps => simp [substitute, evalFormula, eval_substituteAny env rs ps]
  | not p => simp [substitute, evalFormula, eval_substitute env rs p]
  | atom r t u => simp [substitute, evalFormula,
      eval_substituteTerm env rs t, eval_substituteTerm env rs u]
termination_by sizeOf p

/-- The substitution theorem for conjunction parts. -/
theorem eval_substituteAll (env : Name → Int) (rs : List (Name × Term))
    (ps : List Formula) : evalAll env (substituteParts rs ps) =
      evalAll (substitutedEnv env rs) ps := by
  cases ps with
  | nil => simp [substituteParts, evalAll]
  | cons p ps => simp [substituteParts, evalAll,
      eval_substitute env rs p, eval_substituteAll env rs ps]
termination_by sizeOf ps

/-- The substitution theorem for disjunction parts. -/
theorem eval_substituteAny (env : Name → Int) (rs : List (Name × Term))
    (ps : List Formula) : evalAny env (substituteParts rs ps) =
      evalAny (substitutedEnv env rs) ps := by
  cases ps with
  | nil => simp [substituteParts, evalAny]
  | cons p ps => simp [substituteParts, evalAny,
      eval_substitute env rs p, eval_substituteAny env rs ps]
termination_by sizeOf ps
end

/-- An identity entry does not suppress a later replacement of the same name. -/
theorem replacement_ignores_identity (replacements : List (Name × Term)) (name : Name) :
    replacement ((name, .var name) :: replacements) name = replacement replacements name := by
  simp [replacement, active]

/-- The first active replacement wins, including when later entries repeat its name. -/
theorem replacement_first (replacements : List (Name × Term)) (name : Name) (term : Term)
    (different : term ≠ .var name) :
    replacement ((name, term) :: replacements) name = term := by
  simp [replacement, active, lookup, different]

/-- Replacement terms are not rewritten by other entries in the same substitution. -/
theorem substitution_is_simultaneous :
    substituteTerm [("x", .var "y"), ("y", .lit 1)] (.var "x") = .var "y" := by
  simp [substituteTerm, replacement, active, lookup]

/-- Source constructor tags for the derived term order. -/
def termTag : Term → Nat
  | .lit _ => 0 | .var _ => 1 | .neg _ => 2 | .add _ _ => 3
  | .sub _ _ => 4 | .mul _ _ => 5 | .ite _ _ _ => 6

/-- Source constructor tags for the derived formula order. -/
def formulaTag : Formula → Nat
  | .top => 0 | .and _ => 1 | .bottom => 2 | .or _ => 3
  | .not _ => 4 | .atom _ _ _ => 5

/-- Source constructor tags for the derived relation order. -/
def relationTag : Relation → Nat
  | .eq => 0 | .ne => 1 | .gt => 2 | .ge => 3 | .lt => 4 | .le => 5

mutual
/-- Lexicographic order of terms, as in the derived Haskell `Ord` instance. -/
def compareTerm : Term → Term → Ordering
  | .lit a, .lit b => compare a b
  | .var a, .var b => compare a b
  | .neg a, .neg b => compareTerm a b
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d =>
      (compareTerm a c).then (compareTerm b d)
  | .ite p a b, .ite q c d =>
      (compareFormula p q).then ((compareTerm a c).then (compareTerm b d))
  | a, b => compare (termTag a) (termTag b)
termination_by a _ => sizeOf a

/-- Lexicographic order of formulas, including the source constructor order. -/
def compareFormula : Formula → Formula → Ordering
  | .top, .top | .bottom, .bottom => .eq
  | .and ps, .and qs | .or ps, .or qs => compareParts ps qs
  | .not p, .not q => compareFormula p q
  | .atom r a b, .atom s c d =>
      (compare (relationTag r) (relationTag s)).then
        ((compareTerm a c).then (compareTerm b d))
  | p, q => compare (formulaTag p) (formulaTag q)
termination_by p _ => sizeOf p

/-- Lexicographic order of lists of formulas. -/
def compareParts : List Formula → List Formula → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | p :: ps, q :: qs => (compareFormula p q).then (compareParts ps qs)
termination_by ps _ => sizeOf ps
end

/-- The source's syntactic tautology test. It is intentionally incomplete. -/
def tautology : Formula → Bool
  | .top => true
  | .atom .eq a b | .atom .le a b | .atom .ge a b => a == b
  | .atom .ne (.lit a) (.lit b) => a != b
  | _ => false

/-- The source's syntactic contradiction test. It is intentionally incomplete. -/
def contradiction : Formula → Bool
  | .bottom => true
  | .atom .eq (.lit a) (.lit b) => a != b
  | .atom .ne a b => a == b
  | _ => false

/-- Every recognized tautology holds in every integer assignment. -/
theorem tautology_sound (env : Name → Int) (p : Formula)
    (h : tautology p = true) : evalFormula env p = true := by
  cases p with
  | top => simp [evalFormula]
  | and ps => simp [tautology] at h
  | bottom => simp [tautology] at h
  | or ps => simp [tautology] at h
  | not p => simp [tautology] at h
  | atom r a b =>
      cases r with
      | eq => simp only [tautology, beq_iff_eq] at h; subst b
              simp [evalFormula, evalRelation]
      | le => simp only [tautology, beq_iff_eq] at h; subst b
              simp [evalFormula, evalRelation]
      | ge => simp only [tautology, beq_iff_eq] at h; subst b
              simp [evalFormula, evalRelation]
      | gt => simp [tautology] at h
      | lt => simp [tautology] at h
      | ne => cases a <;> cases b <;>
          simp_all [tautology, evalFormula, evalRelation, evalTerm]

/-- Every recognized contradiction fails in every integer assignment. -/
theorem contradiction_sound (env : Name → Int) (p : Formula)
    (h : contradiction p = true) : evalFormula env p = false := by
  cases p with
  | bottom => simp [evalFormula]
  | top => simp [contradiction] at h
  | and ps => simp [contradiction] at h
  | or ps => simp [contradiction] at h
  | not p => simp [contradiction] at h
  | atom r a b =>
      cases r with
      | ne => simp only [contradiction, beq_iff_eq] at h; subst b
              simp [evalFormula, evalRelation]
      | eq => cases a <;> cases b <;>
          simp_all [contradiction, evalFormula, evalRelation, evalTerm]
      | gt | ge | lt | le => simp [contradiction] at h

/-- The custom conjunction fold agrees with `List.all`. -/
theorem evalAll_eq_all (env : Name → Int) (ps : List Formula) :
    evalAll env ps = ps.all (evalFormula env) := by
  induction ps with
  | nil => simp [evalAll]
  | cons p ps ih => simp [evalAll, ih]

/-- The custom disjunction fold agrees with `List.any`. -/
theorem evalAny_eq_any (env : Name → Int) (ps : List Formula) :
    evalAny env ps = ps.any (evalFormula env) := by
  induction ps with
  | nil => simp [evalAny]
  | cons p ps ih => simp [evalAny, ih]

/-- A recognized contradiction makes the whole conjunction false. -/
theorem any_contradiction (env : Name → Int) (ps : List Formula)
    (h : ps.any contradiction = true) : evalAll env ps = false := by
  rw [List.any_eq_true] at h
  rcases h with ⟨p, member, hp⟩
  rw [evalAll_eq_all, List.all_eq_false]
  exact ⟨p, member, by simp [contradiction_sound env p hp]⟩

/-- A recognized tautology makes the whole disjunction true. -/
theorem any_tautology (env : Name → Int) (ps : List Formula)
    (h : ps.any tautology = true) : evalAny env ps = true := by
  rw [List.any_eq_true] at h
  rcases h with ⟨p, member, hp⟩
  rw [evalAny_eq_any, List.any_eq_true]
  exact ⟨p, member, tautology_sound env p hp⟩

/-- Removing recognized tautologies preserves a conjunction. -/
theorem evalAll_filter_tautology (env : Name → Int) (ps : List Formula) :
    evalAll env (ps.filter fun p => !tautology p) = evalAll env ps := by
  induction ps with
  | nil => simp [evalAll]
  | cons p ps ih =>
      cases ht : tautology p <;>
        simp [ht, evalAll, ih, tautology_sound env p]

/-- Removing recognized contradictions preserves a disjunction. -/
theorem evalAny_filter_contradiction (env : Name → Int) (ps : List Formula) :
    evalAny env (ps.filter fun p => !contradiction p) = evalAny env ps := by
  induction ps with
  | nil => simp [evalAny]
  | cons p ps ih =>
      cases hc : contradiction p <;>
        simp [hc, evalAny, ih, contradiction_sound env p]

/-- Flatten nested conjunctions without changing any other formula. -/
def flatten : List Formula → List Formula
  | [] => []
  | .and ps :: rest => flatten ps ++ flatten rest
  | p :: rest => p :: flatten rest
termination_by ps => sizeOf ps

/-- A list append denotes the conjunction of both lists. -/
theorem evalAll_append (env : Name → Int) (ps qs : List Formula) :
    evalAll env (ps ++ qs) = (evalAll env ps && evalAll env qs) := by
  simp [evalAll_eq_all, List.all_append]

/-- Flattening nested conjunctions preserves their meaning. -/
theorem evalAll_flatten (env : Name → Int) (ps : List Formula) :
    evalAll env (flatten ps) = evalAll env ps := by
  cases ps with
  | nil => simp [flatten]
  | cons p rest =>
      cases p with
      | and ps =>
          simp [flatten, evalAll, evalFormula, evalAll_append,
            evalAll_flatten env ps, evalAll_flatten env rest]
      | top | bottom | or ps | not p | atom r a b =>
          simp [flatten, evalAll, evalAll_flatten env rest]
termination_by sizeOf ps

/-- Sort conjunction parts and remove exact structural duplicates. -/
def canonicalParts (ps : List Formula) : List Formula :=
  ps.eraseDups.mergeSort fun p q => (compareFormula p q).isLE

/-- Every original part occurs in the canonical list and conversely. -/
theorem mem_canonicalParts (p : Formula) (ps : List Formula) :
    p ∈ canonicalParts ps ↔ p ∈ ps := by
  simp [canonicalParts]

/-- Sorting and duplicate removal preserve a conjunction. -/
theorem evalAll_canonicalParts (env : Name → Int) (ps : List Formula) :
    evalAll env (canonicalParts ps) = evalAll env ps := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalAll_eq_all, List.all_eq_true, mem_canonicalParts]

/-- The source returns the sole conjunction part without an `And` wrapper. -/
def packAnd : List Formula → Formula
  | [] => .top
  | [p] => p
  | ps => .and ps

/-- The source retains an `Or` wrapper after it removes contradictions. -/
def packOr : List Formula → Formula
  | [] => .bottom
  | ps => .or ps

/-- Remove double negation after simplifying the inner formula. -/
def simplifyNot : Formula → Formula
  | .not p => p
  | p => .not p

/-- The conjunction wrapper preserves the conjunction fold. -/
theorem eval_packAnd (env : Name → Int) (ps : List Formula) :
    evalFormula env (packAnd ps) = evalAll env ps := by
  cases ps with
  | nil => simp [packAnd, evalFormula, evalAll]
  | cons p ps => cases ps <;> simp [packAnd, evalFormula, evalAll]

/-- The disjunction wrapper preserves the disjunction fold. -/
theorem eval_packOr (env : Name → Int) (ps : List Formula) :
    evalFormula env (packOr ps) = evalAny env ps := by
  cases ps <;> simp [packOr, evalFormula, evalAny]

/-- Double-negation elimination preserves negation. -/
theorem eval_simplifyNot (env : Name → Int) (p : Formula) :
    evalFormula env (simplifyNot p) = !(evalFormula env p) := by
  cases p <;> simp [simplifyNot, evalFormula]

mutual
/-- The source simplifier on the integer fragment, including its asymmetric `And` and `Or`. -/
def simplify : Formula → Formula
  | .or [] => .bottom
  | .or [p] => simplify p
  | .not p => simplifyNot (simplify p)
  | .and ps =>
      if ps.any contradiction then .bottom
      else packAnd (canonicalParts (flatten ((simplifyParts ps).filter fun p => !tautology p)))
  | .or ps =>
      if ps.any tautology then .top
      else packOr ((simplifyParts ps).filter fun p => !contradiction p)
  | p => if contradiction p then .bottom else if tautology p then .top else p
termination_by p => sizeOf p

/-- Simplify every part before list-specific normalization. -/
def simplifyParts : List Formula → List Formula
  | [] => []
  | p :: ps => simplify p :: simplifyParts ps
termination_by ps => sizeOf ps
end

mutual
/-- The source simplifier preserves every formula under every integer assignment. -/
theorem eval_simplify (env : Name → Int) (p : Formula) :
    evalFormula env (simplify p) = evalFormula env p := by
  cases p with
  | top => simp [simplify, contradiction, tautology, evalFormula]
  | bottom => simp [simplify, contradiction, evalFormula]
  | not p => simp [simplify, evalFormula, eval_simplifyNot, eval_simplify env p]
  | and ps =>
      simp only [simplify]
      split
      · rename_i h
        simp [evalFormula, any_contradiction env ps h]
      · simp [eval_packAnd, evalAll_canonicalParts, evalAll_flatten,
          evalAll_filter_tautology, eval_simplifyAll env ps, evalFormula]
  | or ps =>
      cases ps with
      | nil => simp [simplify, evalFormula, evalAny]
      | cons p ps =>
          cases ps with
          | nil => simp [simplify, evalFormula, evalAny, eval_simplify env p]
          | cons q qs =>
              simp only [simplify]
              split
              · rename_i h
                simp [evalFormula, any_tautology env (p :: q :: qs) h]
              · simp [eval_packOr, evalAny_filter_contradiction,
                  eval_simplifyAny env (p :: q :: qs), evalFormula]
  | atom r a b =>
      simp only [simplify]
      split
      · rename_i h
        simp [evalFormula, ← contradiction_sound env (.atom r a b) h]
      · split
        · rename_i h
          simp [evalFormula, ← tautology_sound env (.atom r a b) h]
        · rfl
termination_by sizeOf p

/-- Simplifying all conjunction parts preserves their conjunction. -/
theorem eval_simplifyAll (env : Name → Int) (ps : List Formula) :
    evalAll env (simplifyParts ps) = evalAll env ps := by
  cases ps with
  | nil => simp [simplifyParts, evalAll]
  | cons p ps => simp [simplifyParts, evalAll, eval_simplify env p, eval_simplifyAll env ps]
termination_by sizeOf ps

/-- Simplifying all disjunction parts preserves their disjunction. -/
theorem eval_simplifyAny (env : Name → Int) (ps : List Formula) :
    evalAny env (simplifyParts ps) = evalAny env ps := by
  cases ps with
  | nil => simp [simplifyParts, evalAny]
  | cons p ps => simp [simplifyParts, evalAny, eval_simplify env p, eval_simplifyAny env ps]
termination_by sizeOf ps
end

/-- The source's conjunction smart constructor. -/
def conjunction (ps : List Formula) : Formula := simplify (.and ps)

/-- The source's disjunction smart constructor. -/
def disjunction (ps : List Formula) : Formula := simplify (.or ps)

/-- Unsimplified implication, as in `implies`. -/
def implies (p q : Formula) : Formula := .or [.not p, q]

/-- Unsimplified equivalence, as in `iff`. -/
def iff (p q : Formula) : Formula := .or [.and [p, q], .and [.not p, .not q]]

/-- The conjunction smart constructor accepts exactly the common assignments. -/
theorem eval_conjunction (env : Name → Int) (ps : List Formula) :
    evalFormula env (conjunction ps) = ps.all (evalFormula env) := by
  simp [conjunction, eval_simplify, evalFormula, evalAll_eq_all]

/-- The disjunction smart constructor accepts exactly the union of assignments. -/
theorem eval_disjunction (env : Name → Int) (ps : List Formula) :
    evalFormula env (disjunction ps) = ps.any (evalFormula env) := by
  simp [disjunction, eval_simplify, evalFormula, evalAny_eq_any]

/-- The source implication has the usual material-implication semantics. -/
theorem eval_implies (env : Name → Int) (p q : Formula) :
    evalFormula env (implies p q) = (!evalFormula env p || evalFormula env q) := by
  simp [implies, evalFormula, evalAny]

/-- The source equivalence holds exactly when both Boolean meanings agree. -/
theorem eval_iff (env : Name → Int) (p q : Formula) :
    evalFormula env (iff p q) = (evalFormula env p == evalFormula env q) := by
  simp only [iff, evalFormula, evalAny, evalAll]
  cases evalFormula env p <;> cases evalFormula env q <;> rfl

mutual
/-- Collect term names, including names in the condition of `ite`. -/
def termNames : Term → List Name
  | .lit _ => []
  | .var name => [name]
  | .neg t => termNames t
  | .add t u | .sub t u | .mul t u => termNames t ++ termNames u
  | .ite p t u => formulaNames p ++ termNames t ++ termNames u
termination_by t => sizeOf t

/-- Collect formula names before duplicate removal. -/
def formulaNames : Formula → List Name
  | .top | .bottom => []
  | .and ps | .or ps => partsNames ps
  | .not p => formulaNames p
  | .atom _ t u => termNames t ++ termNames u
termination_by p => sizeOf p

/-- Collect the names of every list part. -/
def partsNames : List Formula → List Name
  | [] => []
  | p :: ps => formulaNames p ++ partsNames ps
termination_by ps => sizeOf ps
end

/-- The source free-name set. List order abstracts the Haskell hash-set order. -/
def freeNames (p : Formula) : List Name := (formulaNames p).eraseDups

/-- A free name occurs in the formula syntax. Duplicate removal loses no name. -/
theorem mem_freeNames (name : Name) (p : Formula) :
    name ∈ freeNames p ↔ name ∈ formulaNames p := by
  simp [freeNames]

private theorem eraseDups_nodup (names : List Name) : names.eraseDups.Nodup := by
  cases names with
  | nil => simp
  | cons name names =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (names.filter fun other => !(other == name))
termination_by names.length
decreasing_by
  have h := List.length_filter_le (fun other => !(other == name)) names
  simp only [List.length_cons]
  omega

/-- The free-name representation contains no repeated name. -/
theorem freeNames_nodup (p : Formula) : (freeNames p).Nodup := by
  exact eraseDups_nodup _

mutual
/-- A term depends only on names that occur in its complete syntax. -/
theorem evalTerm_ext (left right : Name → Int) (t : Term)
    (same : ∀ name ∈ termNames t, left name = right name) :
    evalTerm left t = evalTerm right t := by
  cases t with
  | lit n => simp [evalTerm]
  | var name => simpa [evalTerm] using same name (by simp [termNames])
  | neg t =>
      simp only [evalTerm]
      rw [evalTerm_ext left right t (by simpa [termNames] using same)]
  | add t u =>
      simp only [evalTerm]
      rw [evalTerm_ext left right t (fun n h => same n (by simp [termNames, h])),
          evalTerm_ext left right u (fun n h => same n (by simp [termNames, h]))]
  | sub t u =>
      simp only [evalTerm]
      rw [evalTerm_ext left right t (fun n h => same n (by simp [termNames, h])),
          evalTerm_ext left right u (fun n h => same n (by simp [termNames, h]))]
  | mul t u =>
      simp only [evalTerm]
      rw [evalTerm_ext left right t (fun n h => same n (by simp [termNames, h])),
          evalTerm_ext left right u (fun n h => same n (by simp [termNames, h]))]
  | ite p t u =>
      simp only [evalTerm]
      rw [evalFormula_ext left right p (fun n h => same n (by simp [termNames, h])),
          evalTerm_ext left right t (fun n h => same n (by simp [termNames, h])),
          evalTerm_ext left right u (fun n h => same n (by simp [termNames, h]))]
termination_by sizeOf t

/-- Formula truth depends only on syntactically occurring names. -/
theorem evalFormula_ext (left right : Name → Int) (p : Formula)
    (same : ∀ name ∈ formulaNames p, left name = right name) :
    evalFormula left p = evalFormula right p := by
  cases p with
  | top => simp [evalFormula]
  | bottom => simp [evalFormula]
  | and ps =>
      simp only [evalFormula]
      exact evalAll_ext left right ps (by simpa [formulaNames] using same)
  | or ps =>
      simp only [evalFormula]
      exact evalAny_ext left right ps (by simpa [formulaNames] using same)
  | not p =>
      simp only [evalFormula]
      rw [evalFormula_ext left right p (by simpa [formulaNames] using same)]
  | atom r t u =>
      simp only [evalFormula]
      rw [evalTerm_ext left right t (fun n h => same n (by simp [formulaNames, h])),
          evalTerm_ext left right u (fun n h => same n (by simp [formulaNames, h]))]
termination_by sizeOf p

/-- Conjunction truth depends only on the names of its parts. -/
theorem evalAll_ext (left right : Name → Int) (ps : List Formula)
    (same : ∀ name ∈ partsNames ps, left name = right name) :
    evalAll left ps = evalAll right ps := by
  cases ps with
  | nil => simp [evalAll]
  | cons p ps =>
      simp only [evalAll]
      rw [evalFormula_ext left right p (fun n h => same n (by simp [partsNames, h])),
          evalAll_ext left right ps (fun n h => same n (by simp [partsNames, h]))]
termination_by sizeOf ps

/-- Disjunction truth depends only on the names of its parts. -/
theorem evalAny_ext (left right : Name → Int) (ps : List Formula)
    (same : ∀ name ∈ partsNames ps, left name = right name) :
    evalAny left ps = evalAny right ps := by
  cases ps with
  | nil => simp [evalAny]
  | cons p ps =>
      simp only [evalAny]
      rw [evalFormula_ext left right p (fun n h => same n (by simp [partsNames, h])),
          evalAny_ext left right ps (fun n h => same n (by simp [partsNames, h]))]
termination_by sizeOf ps
end

/-- Agreement on `freeNames` suffices for identical truth values. -/
theorem evalFormula_freeNames (left right : Name → Int) (p : Formula)
    (same : ∀ name ∈ freeNames p, left name = right name) :
    evalFormula left p = evalFormula right p := by
  apply evalFormula_ext left right p
  intro name member
  exact same name ((mem_freeNames name p).mpr member)

/-- The singleton left after filtering an `Or` keeps its wrapper for one pass. -/
theorem disjunction_retains_singleton :
    disjunction [.bottom, .atom .gt (.var "x") (.lit 0)] =
      .or [.atom .gt (.var "x") (.lit 0)] := by
  simp [disjunction, simplify, simplifyParts, tautology, contradiction, packOr]

/-- The source simplifier is not an idempotent canonicalization function. -/
theorem simplify_not_idempotent :
    ∃ p, simplify (simplify p) ≠ simplify p := by
  refine ⟨.or [.bottom, .atom .gt (.var "x") (.lit 0)], ?_⟩
  have h := disjunction_retains_singleton
  unfold disjunction at h
  rw [h]
  simp [simplify, contradiction, tautology]

/-- Syntactic inequality does not imply a difference in accepted assignments. -/
theorem structural_equality_is_not_semantic_equality :
    Formula.not .top ≠ Formula.bottom ∧
      ∀ env, evalFormula env (.not .top) = evalFormula env .bottom := by
  constructor
  · intro h; cases h
  · intro env; simp [evalFormula]

end MicroCFTA.CoreFormula
