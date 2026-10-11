import MicroCFTA.Language
import MicroCFTA.CoreFormula

/-!
# Compile a constrained grammar to a tree automaton

A grammar has named nonterminals and nested constructor patterns. Each
constructor has a decidable predicate over its complete output tree.
`Derives` is the finite source-language judgment. `compile` emits transitions
and uses pattern states for nested constructors. References can be cyclic.

The compiler does not assume that a finite language has already been
constructed. The soundness and completeness theorem relates the independent
grammar judgment to the resulting automaton's finite-run semantics.
-/

namespace MicroCFTA.Construction

open Language

/-- A decidable semantic constraint on the complete term at one constructor. -/
structure Constraint (Symbol : Type) where
  holds : Term Symbol → Prop
  decision : ∀ term, Decidable (holds term)

/-- Compile a semantic constraint to the Boolean guard expected by an FTA. -/
def Constraint.test (constraint : Constraint Symbol) (term : Term Symbol) : Bool :=
  @decide (constraint.holds term) (constraint.decision term)

/-- Guard compilation preserves the declared constraint exactly. -/
theorem Constraint.test_correct (constraint : Constraint Symbol) (term : Term Symbol) :
    constraint.test term = true ↔ constraint.holds term := by
  exact Iff.of_eq (@decide_eq_true_eq _ (constraint.decision term))

/-- The unconstrained constructor accepts every complete term. -/
def Constraint.top : Constraint Symbol := ⟨fun _ => True, fun _ => inferInstance⟩

/-- A positive path equality requires equal, existing subtrees. -/
def Constraint.equal [DecidableEq Symbol] (left right : List Nat) : Constraint Symbol :=
  ⟨fun term => PathsEqual term left right,
    fun term => decidable_of_iff (pathEquality left right term = true)
      (pathEquality_correct left right term)⟩

/-- Conjunction preserves both semantic requirements. -/
def Constraint.and (left right : Constraint Symbol) : Constraint Symbol :=
  ⟨fun term => left.holds term ∧ right.holds term,
    fun term => @instDecidableAnd _ _ (left.decision term) (right.decision term)⟩

/-- Disjunction accepts either semantic requirement. -/
def Constraint.or (left right : Constraint Symbol) : Constraint Symbol :=
  ⟨fun term => left.holds term ∨ right.holds term,
    fun term => @instDecidableOr _ _ (left.decision term) (right.decision term)⟩

/-- Negation complements the complete semantic requirement, including path existence. -/
def Constraint.not (inner : Constraint Symbol) : Constraint Symbol :=
  ⟨fun term => ¬inner.holds term, fun term => @instDecidableNot _ (inner.decision term)⟩

/-- A nested constructor pattern can refer to a named grammar nonterminal. -/
inductive Pattern (Nonterminal Symbol : Type) where
  | reference : Nonterminal → Pattern Nonterminal Symbol
  | constructor : Symbol → List (Pattern Nonterminal Symbol) → Constraint Symbol →
      Pattern Nonterminal Symbol

/-- A production consumes one constructor before any nonterminal recursion. -/
structure Production (Nonterminal Symbol : Type) where
  symbol : Symbol
  children : List (Pattern Nonterminal Symbol)
  constraint : Constraint Symbol

/-- A finite list of alternatives at each named nonterminal. -/
abbrev Grammar (Nonterminal Symbol : Type) := Nonterminal → List (Production Nonterminal Symbol)

/-- Treat a production body as a nested constructor pattern. -/
def Production.pattern (production : Production Nonterminal Symbol) : Pattern Nonterminal Symbol :=
  .constructor production.symbol production.children production.constraint

/-- The language declared by the grammar. No automaton appears in this definition. -/
inductive Derives (grammar : Grammar Nonterminal Symbol) :
    Pattern Nonterminal Symbol → Term Symbol → Prop where
  | reference (production : Production Nonterminal Symbol) (term : Term Symbol) :
      production ∈ grammar name → Derives grammar production.pattern term →
      Derives grammar (.reference name) term
  | constructor (symbol : Symbol) (patterns : List (Pattern Nonterminal Symbol))
      (constraint : Constraint Symbol) (terms : List (Term Symbol)) :
      All₂ (Derives grammar) patterns terms → constraint.holds (.node symbol terms) →
      Derives grammar (.constructor symbol patterns constraint) (.node symbol terms)

/-- A production becomes one transition to its child pattern states. -/
def Production.edge (production : Production Nonterminal Symbol) :
    Edge (Pattern Nonterminal Symbol) Symbol :=
  ⟨production.symbol, production.children, production.constraint.test⟩

/-- Compile nested patterns and named references. No terms are enumerated. -/
def compile (grammar : Grammar Nonterminal Symbol) :
    Automaton (Pattern Nonterminal Symbol) Symbol
  | .reference name => (grammar name).map Production.edge
  | .constructor symbol children constraint => [⟨symbol, children, constraint.test⟩]

/-- Every source-language derivation has an accepting compiled run. -/
theorem compile_complete (grammar : Grammar Nonterminal Symbol)
    {pattern : Pattern Nonterminal Symbol} {term : Term Symbol}
    (derived : Derives grammar pattern term) : Accepts (compile grammar) pattern term := by
  induction derived using Derives.rec
    (motive_2 := fun patterns terms _ => All₂ (Accepts (compile grammar)) patterns terms) with
  | reference production term member derived ih =>
      cases ih with
      | node edge terms edgeMember children guard =>
          have same : edge = production.edge := List.mem_singleton.mp edgeMember
          subst edge
          exact .node production.edge terms
            (List.mem_map.mpr ⟨production, member, rfl⟩) children guard
  | constructor symbol patterns constraint terms children holds ih =>
      exact .node ⟨symbol, patterns, constraint.test⟩ terms (by simp [compile]) ih
        ((constraint.test_correct _).mpr holds)
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

/-- Every accepting compiled run has a derivation in the declared language. -/
theorem compile_sound (grammar : Grammar Nonterminal Symbol)
    {pattern : Pattern Nonterminal Symbol} {term : Term Symbol}
    (accepted : Accepts (compile grammar) pattern term) : Derives grammar pattern term := by
  induction accepted using Accepts.rec
    (motive_2 := fun patterns terms _ => All₂ (Derives grammar) patterns terms) with
  | @node pattern edge terms member children guard ih =>
      cases pattern with
      | reference name =>
          obtain ⟨production, productionMember, same⟩ := List.mem_map.mp member
          subst edge
          apply Derives.reference production _ productionMember
          exact .constructor production.symbol production.children production.constraint terms ih
            ((production.constraint.test_correct _).mp guard)
      | constructor symbol patterns constraint =>
          have same : edge = ⟨symbol, patterns, constraint.test⟩ := List.mem_singleton.mp member
          subst edge
          exact .constructor symbol patterns constraint terms ih
            ((constraint.test_correct _).mp guard)
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

/-- Compilation preserves all and only the declared finite terms, even with recursive references. -/
theorem compile_exact (grammar : Grammar Nonterminal Symbol)
    (pattern : Pattern Nonterminal Symbol) (term : Term Symbol) :
    Accepts (compile grammar) pattern term ↔ Derives grammar pattern term :=
  ⟨compile_sound grammar, compile_complete grammar⟩

/-- Bounded compiled enumeration has exact soundness and completeness. -/
theorem compiled_enumeration_exact (grammar : Grammar Nonterminal Symbol)
    (pattern : Pattern Nonterminal Symbol) (term : Term Symbol) (fuel : Nat) :
    term ∈ enumerate (compile grammar) fuel pattern ↔
      Derives grammar pattern term ∧ term.height ≤ fuel := by
  rw [mem_enumerate_iff, compile_exact]

/-- Every valid finite expression eventually appears; no fixed depth bound is assumed. -/
theorem derives_iff_eventually_enumerated (grammar : Grammar Nonterminal Symbol)
    (pattern : Pattern Nonterminal Symbol) (term : Term Symbol) :
    Derives grammar pattern term ↔ ∃ fuel, term ∈ enumerate (compile grammar) fuel pattern := by
  rw [← compile_exact, accepts_iff_eventually_enumerated]

/-- List all constructor and reference subpatterns of one finite pattern. -/
def subpatterns : Pattern Nonterminal Symbol → List (Pattern Nonterminal Symbol)
  | .reference name => [.reference name]
  | .constructor symbol children constraint =>
      .constructor symbol children constraint :: children.flatMap subpatterns

/-- A pattern occurs in its own finite subpattern list. -/
theorem self_mem_subpatterns (pattern : Pattern Nonterminal Symbol) :
    pattern ∈ subpatterns pattern := by
  cases pattern <;> simp [subpatterns]

/-- The subpattern list is closed under further descent. -/
theorem subpatterns_transitive (pattern inner leaf : Pattern Nonterminal Symbol)
    (inside : inner ∈ subpatterns pattern) (below : leaf ∈ subpatterns inner) :
    leaf ∈ subpatterns pattern := by
  induction pattern using Pattern.rec
    (motive_2 := fun patterns => ∀ inner leaf,
      inner ∈ patterns.flatMap subpatterns → leaf ∈ subpatterns inner →
      leaf ∈ patterns.flatMap subpatterns) generalizing inner leaf with
  | reference name =>
      simp only [subpatterns] at inside
      have same : inner = .reference name := List.mem_singleton.mp inside
      simpa [same] using below
  | constructor symbol children constraint ih =>
      simp only [subpatterns] at inside ⊢
      rcases List.mem_cons.mp inside with same | inside
      · subst inner
        simpa only [subpatterns] using below
      · exact List.mem_cons_of_mem _ (ih inner leaf inside below)
  | nil inner leaf inside below => simp at inside
  | cons first rest ihfirst ihrest inner leaf inside below =>
      rcases List.mem_append.mp inside with inside | inside
      · exact List.mem_append_left _ (ihfirst inner leaf inside below)
      · exact List.mem_append_right _ (ihrest inner leaf inside below)

/-- A finite state list for a grammar whose nonterminal names have a finite listing. -/
def states (grammar : Grammar Nonterminal Symbol) (names : List Nonterminal) :
    List (Pattern Nonterminal Symbol) :=
  names.map Pattern.reference ++ names.flatMap fun name =>
    (grammar name).flatMap fun production => subpatterns production.pattern

/-- Every named start state occurs in the compiled state list. -/
theorem reference_mem_states (grammar : Grammar Nonterminal Symbol) (names : List Nonterminal)
    (name : Nonterminal) (listed : name ∈ names) : Pattern.reference name ∈ states grammar names := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨name, listed, rfl⟩)

/-- All subpatterns of every listed production are available compiled states. -/
theorem production_subpattern_mem_states (grammar : Grammar Nonterminal Symbol)
    (names : List Nonterminal) (name : Nonterminal) (production : Production Nonterminal Symbol)
    (pattern : Pattern Nonterminal Symbol) (listed : name ∈ names)
    (alternative : production ∈ grammar name) (inside : pattern ∈ subpatterns production.pattern) :
    pattern ∈ states grammar names := by
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨name, listed,
    List.mem_flatMap.mpr ⟨production, alternative, inside⟩⟩)

/-- The compiled state list is closed under all transitions.
Only the nonterminal list must be finite. Recursive references remain allowed. -/
theorem compiled_states_closed (grammar : Grammar Nonterminal Symbol)
    (names : List Nonterminal) (complete : ∀ name, name ∈ names)
    (pattern : Pattern Nonterminal Symbol) (edge : Edge (Pattern Nonterminal Symbol) Symbol)
    (present : pattern ∈ states grammar names) (transition : edge ∈ compile grammar pattern)
    (child : Pattern Nonterminal Symbol) (childMember : child ∈ edge.children) :
    child ∈ states grammar names := by
  cases pattern with
  | reference name =>
      obtain ⟨production, alternative, same⟩ := List.mem_map.mp transition
      subst edge
      apply production_subpattern_mem_states grammar names name production child (complete name) alternative
      simp only [Production.pattern, subpatterns]
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨child, childMember, self_mem_subpatterns child⟩
  | constructor symbol children constraint =>
      have same : edge = ⟨symbol, children, constraint.test⟩ := List.mem_singleton.mp transition
      subst edge
      obtain (impossible | present) := List.mem_append.mp present
      · obtain ⟨name, _, impossible⟩ := List.mem_map.mp impossible
        cases impossible
      · obtain ⟨name, listed, production, alternative, inside⟩ :=
          (by simpa only [List.mem_flatMap] using present :
            ∃ name, name ∈ names ∧ ∃ production, production ∈ grammar name ∧
              Pattern.constructor symbol children constraint ∈ subpatterns production.pattern)
        apply production_subpattern_mem_states grammar names name production child listed alternative
        apply subpatterns_transitive _ (.constructor symbol children constraint) child inside
        simp only [subpatterns]
        exact List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨child, childMember, self_mem_subpatterns child⟩)

/-- A ground liquid formula uses the declared integer interpretation of a complete term.
This is formula evaluation. It does not call an SMT entailment solver. -/
def Constraint.groundFormula (environment : Term Symbol → CoreFormula.Name → Int)
    (formula : CoreFormula.Formula) : Constraint Symbol :=
  ⟨fun term => CoreFormula.evalFormula (environment term) formula = true,
    fun _ => inferInstance⟩

/-- Ground formula compilation runs the complete integer formula interpreter. -/
theorem Constraint.groundFormula_test (environment : Term Symbol → CoreFormula.Name → Int)
    (formula : CoreFormula.Formula) (term : Term Symbol) :
    (Constraint.groundFormula environment formula).test term =
      CoreFormula.evalFormula (environment term) formula := by
  cases h : CoreFormula.evalFormula (environment term) formula <;>
    simp [Constraint.test, Constraint.groundFormula, h]

/-- Simplifying a liquid formula preserves its compiled language at each constructor. -/
theorem Constraint.simplify_groundFormula (environment : Term Symbol → CoreFormula.Name → Int)
    (formula : CoreFormula.Formula) (term : Term Symbol) :
    (Constraint.groundFormula environment (CoreFormula.simplify formula)).holds term ↔
      (Constraint.groundFormula environment formula).holds term := by
  simp only [Constraint.groundFormula, CoreFormula.eval_simplify]

/-- A finite recursive example. It derives zero or any finite number of successors. -/
def unaryGrammar : Grammar Unit Nat := fun _ =>
  [⟨0, [], .top⟩, ⟨1, [.reference ()], .top⟩]

/-- The tree for the natural number encoded by the recursive grammar. -/
def unaryTerm : Nat → Term Nat
  | 0 => .node 0 []
  | n + 1 => .node 1 [unaryTerm n]

/-- Recursive named references preserve arbitrarily deep finite expressions. -/
theorem unaryGrammar_complete (n : Nat) :
    Derives unaryGrammar (.reference ()) (unaryTerm n) := by
  induction n with
  | zero =>
      apply Derives.reference ⟨0, [], .top⟩ _ (by simp [unaryGrammar])
      exact .constructor 0 [] .top [] .nil trivial
  | succ n ih =>
      apply Derives.reference ⟨1, [.reference ()], .top⟩ _ (by simp [unaryGrammar])
      exact .constructor 1 [.reference ()] .top [unaryTerm n] (.cons ih .nil) trivial

/-- Cyclic grammar compilation still enumerates every finite member at a finite bound. -/
theorem unaryGrammar_enumerates (n : Nat) :
    ∃ fuel, unaryTerm n ∈ enumerate (compile unaryGrammar) fuel (.reference ()) :=
  (derives_iff_eventually_enumerated _ _ _).mp (unaryGrammar_complete n)

/-- Two leaves and a pair constructor with an exact child equality. -/
def equalPairGrammar : Grammar Bool Nat
  | false => [⟨2, [.reference true, .reference true], .equal [0] [1]⟩]
  | true => [⟨0, [], .top⟩, ⟨1, [], .top⟩]

/-- Equality grammar compilation retains both valid pairs and rejects the mixed pairs. -/
theorem equalPairGrammar_enumeration :
    enumerate (compile equalPairGrammar) 2 (.reference false) =
      [.node 2 [.node 0 [], .node 0 []], .node 2 [.node 1 [], .node 1 []]] := by
  rfl

/-- Interpret the symbol of an integer tree as each queried integer name. -/
def rootInteger : Term Int → CoreFormula.Name → Int
  | .node value _, _ => value

/-- Three integer alternatives share the liquid requirement `value >= 0`. -/
def nonnegativeGrammar : Grammar Unit Int := fun _ =>
  [-1, 0, 1].map fun value =>
    ⟨value, [], .groundFormula rootInteger (.atom .ge (.var "value") (.lit 0))⟩

/-- Ground liquid compilation rejects the negative alternative and retains zero. -/
theorem nonnegativeGrammar_enumeration :
    enumerate (compile nonnegativeGrammar) 1 (.reference ()) = [.node 0 [], .node 1 []] := by
  simp [enumerate, compile, nonnegativeGrammar, Production.edge, products,
    Constraint.groundFormula_test, rootInteger, CoreFormula.evalFormula,
    CoreFormula.evalTerm, CoreFormula.evalRelation]

end MicroCFTA.Construction
