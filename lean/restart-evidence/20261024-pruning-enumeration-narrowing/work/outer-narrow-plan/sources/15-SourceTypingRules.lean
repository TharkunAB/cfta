import MicroCFTA.Language

/-!
# Source typing-rule rows and independent bounded derivations

Constructor labels and fixed terms are supplied as resolved candidate data.
Source name and field validation remain separate.
The row model retains source alternative order and exact environment positions.
It does not model validation errors, datatype codecs, the row-map traversal,
or lazy automaton import. Fixed fields retain their complete literal trees.
A separate fixed-value law is needed for the advertised typing domain.
-/
namespace MicroCFTA.SourceTypingRules
open Language
variable {Ty Symbol : Type}

/-- A field is a typed subterm or one fixed encoded value. -/
inductive Child (Ty Symbol : Type) where
  | subterm (binds : List Ty) (typ : Ty)
  | value (term : Term Symbol)

/-- Source rules retain ordinary alternatives and position-indexed variable schemas. -/
inductive Rule (Ty Symbol : Type) where
  | ordinary (label : Symbol) (children : List (Child Ty Symbol)) (result : Ty)
  | variable (label : Symbol) (fields : Nat → Ty → List (Child Ty Symbol))

/-- Typed goals keep innermost-first environments and the signed source nesting bound. -/
inductive Goal (Ty Symbol : Type) where
  | root
  | typed (env : List Ty) (typ : Ty) (remaining : Int)
  | fixed (term : Term Symbol)

/-- Only a Subterm field consumes typing nesting. -/
def Child.isSubterm : Child Ty Symbol → Bool
  | .subterm .. => true
  | .value _ => false

/-- A nonpositive bound admits only alternatives with no Subterm field. -/
def nests (remaining : Int) (children : List (Child Ty Symbol)) : Bool :=
  decide (0 < remaining) || !(children.any Child.isSubterm)

/-- Bound variables are added before the current innermost-first environment. -/
def childGoal (env : List Ty) (remaining : Int) : Child Ty Symbol → Goal Ty Symbol
  | .subterm binds typ => .typed (binds ++ env) typ (remaining - 1)
  | .value term => .fixed term

/-- Ordinary alternatives are selected before all variable alternatives. -/
def ordinarySelected [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (goal : Ty) (remaining : Int) :
    List (Symbol × List (Child Ty Symbol)) :=
  rules.flatMap fun rule => match rule with
  | .ordinary label children result => if result = goal ∧ nests remaining children = true then [(label, children)] else []
  | .variable .. => []

/-- Variable alternatives follow source rule order and then increasing environment positions. -/
def variableSelected [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (goal : Ty) (remaining : Int) :
    List (Symbol × List (Child Ty Symbol)) :=
  rules.flatMap fun rule => match rule with
  | .ordinary .. => []
  | .variable label fields => env.zipIdx.flatMap fun position =>
      if position.1 = goal ∧ nests remaining (fields position.2 position.1) = true then [(label, fields position.2 position.1)] else []

/-- The completed source selection concatenates the two literal alternative groups. -/
def selected [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (goal : Ty) (remaining : Int) :
    List (Symbol × List (Child Ty Symbol)) :=
  ordinarySelected rules goal remaining ++ variableSelected rules env goal remaining

/-- Each selected constructor keeps the exact field order and emits no constraint. -/
def typedRow [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (goal : Ty) (remaining : Int) :
    List (Language.Edge (Goal Ty Symbol) Symbol) :=
  (selected rules env goal remaining).map fun alternative =>
    ⟨alternative.1, alternative.2.map (childGoal env remaining), fun _ => true⟩

/-- Root rows inline deduplicated goals; fixed rows expose the complete literal tree. -/
def row [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int) :
    Automaton (Goal Ty Symbol) Symbol
  | .root => roots.eraseDups.flatMap fun typ => typedRow rules [] typ bound
  | .typed env typ remaining => typedRow rules env typ remaining
  | .fixed (.node label children) => [⟨label, children.map Goal.fixed, fun _ => true⟩]

mutual
  /-- Independent typing uses ordinary rules or the matching de Bruijn environment position. -/
  inductive Typed (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) :
      List Ty → Ty → Int → Term Symbol → Prop where
    | ordinary (rule : Rule.ordinary label children typ ∈ rules)
        (fields : FieldsTyped fixedAllowed rules env remaining children terms) :
        Typed fixedAllowed rules env typ remaining (.node label terms)
    | variable (rule : Rule.variable label schema ∈ rules) (position : env[index]? = some typ)
        (fields : FieldsTyped fixedAllowed rules env remaining (schema index typ) terms) :
        Typed fixedAllowed rules env typ remaining (.node label terms)

  /-- Subterms consume one positive nesting level; fixed fields require their independent validity law. -/
  inductive FieldTyped (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) :
      List Ty → Int → Child Ty Symbol → Term Symbol → Prop where
    | subterm (positive : 0 < remaining)
        (typed : Typed fixedAllowed rules (binds ++ env) typ (remaining - 1) term) :
        FieldTyped fixedAllowed rules env remaining (.subterm binds typ) term
    | value (allowed : fixedAllowed term) : FieldTyped fixedAllowed rules env remaining (.value term) term

  /-- Independent field derivations retain the source field order. -/
  inductive FieldsTyped (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) :
      List Ty → Int → List (Child Ty Symbol) → List (Term Symbol) → Prop where
    | nil : FieldsTyped fixedAllowed rules env remaining [] []
    | cons (first : FieldTyped fixedAllowed rules env remaining child term)
        (rest : FieldsTyped fixedAllowed rules env remaining children terms) :
        FieldsTyped fixedAllowed rules env remaining (child :: children) (term :: terms)
end

/-- Lawful rule data excludes fixed-value injections outside the intended typing domain. -/
def LawfulFixed (fixedAllowed : Term Symbol → Prop) (rules : List (Rule Ty Symbol)) : Prop :=
  (∀ label children typ, Rule.ordinary label children typ ∈ rules →
    ∀ term, Child.value term ∈ children → fixedAllowed term) ∧
  (∀ label schema, Rule.variable label schema ∈ rules →
    ∀ index typ term, Child.value term ∈ schema index typ → fixedAllowed term)


/-- Every selected alternative passed the source nesting filter. -/
theorem selected_nests [DecidableEq Ty] (rules : List (Rule Ty Symbol)) (env : List Ty) (typ : Ty) (remaining : Int)
    (alternative : Symbol × List (Child Ty Symbol)) (member : alternative ∈ selected rules env typ remaining) :
    nests remaining alternative.2 = true := by
  rcases List.mem_append.mp member with ordinary | varCase
  · obtain ⟨rule, _, found⟩ := List.mem_flatMap.mp ordinary
    cases rule with
    | ordinary label children result =>
        dsimp only at found
        split at found <;> simp_all
    | «variable» => cases found
  · obtain ⟨rule, _, found⟩ := List.mem_flatMap.mp varCase
    cases rule with
    | ordinary => cases found
    | «variable» label fields =>
        obtain ⟨⟨actual, index⟩, _, found⟩ := List.mem_flatMap.mp found
        dsimp only at found
        split at found
        · rename_i kept
          have same : alternative = (label, fields index actual) := by simpa only [List.mem_singleton] using found
          rw [same]
          exact kept.2
        · cases found

end MicroCFTA.SourceTypingRules
