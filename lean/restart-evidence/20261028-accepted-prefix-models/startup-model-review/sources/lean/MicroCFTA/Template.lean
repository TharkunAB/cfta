import MicroCFTA.Language

/-!
# Template matching and graph restriction

The five constructors and child alignment follow `Data.CFTA.Template`.
The restricted graph pairs each input state with its requested template.
It keeps each source guard. The language theorem includes cyclic graphs.
-/

namespace MicroCFTA.Template

open Language

/-- Complete-subtree, exact-node, and prefix-node patterns. -/
inductive Pattern (Symbol : Type) where
  | hole
  | anyNode (children : List (Pattern Symbol))
  | node (symbol : Symbol) (children : List (Pattern Symbol))
  | anyPrefix (children : List (Pattern Symbol))
  | prefix (symbol : Symbol) (children : List (Pattern Symbol))

/-- Require an exact child count. -/
def exactChildren (patterns : List (Pattern Symbol)) (arity : Nat) : Option (List (Pattern Symbol)) :=
  if patterns.length = arity then some patterns else none

/-- Extend a child prefix with unrestricted holes. -/
def prefixChildren (patterns : List (Pattern Symbol)) (arity : Nat) : Option (List (Pattern Symbol)) :=
  if patterns.length ≤ arity then some (patterns ++ List.replicate (arity - patterns.length) .hole) else none

/-- Match a constructor and give one template for every child. -/
def childTemplates [DecidableEq Symbol] (pattern : Pattern Symbol) (symbol : Symbol)
    (arity : Nat) : Option (List (Pattern Symbol)) :=
  match pattern with
  | .hole => some (List.replicate arity .hole)
  | .anyNode patterns => exactChildren patterns arity
  | .node wanted patterns => if wanted = symbol then exactChildren patterns arity else none
  | .anyPrefix patterns => prefixChildren patterns arity
  | .prefix wanted patterns => if wanted = symbol then prefixChildren patterns arity else none

/-- Successful child alignment neither omits nor adds a child. -/
theorem childTemplates_length [DecidableEq Symbol] (pattern : Pattern Symbol)
    (symbol : Symbol) (arity : Nat) (patterns : List (Pattern Symbol))
    (aligned : childTemplates pattern symbol arity = some patterns) : patterns.length = arity := by
  cases pattern <;> simp only [childTemplates] at aligned
  · cases aligned; simp
  · unfold exactChildren at aligned
    split at aligned <;> simp_all
  · split at aligned
    · unfold exactChildren at aligned
      split at aligned <;> simp_all
    · simp at aligned
  · unfold prefixChildren at aligned
    split at aligned
    · cases aligned
      simp
      omega
    · simp at aligned
  · split at aligned
    · unfold prefixChildren at aligned
      split at aligned
      · cases aligned
        simp
        omega
      · simp at aligned
    · simp at aligned

/-- A pattern matches a complete term when all aligned child patterns match. -/
inductive Matches [DecidableEq Symbol] : Pattern Symbol → Term Symbol → Prop where
  | node (pattern : Pattern Symbol) (symbol : Symbol) (terms : List (Term Symbol))
      (patterns : List (Pattern Symbol)) :
      childTemplates pattern symbol terms.length = some patterns →
      All₂ Matches patterns terms → Matches pattern (.node symbol terms)

/-- Every complete term matches a hole. -/
theorem hole_matches [DecidableEq Symbol] (term : Term Symbol) : Matches .hole term := by
  induction term using Term.rec
    (motive_2 := fun (terms : List (Term Symbol)) =>
      All₂ Matches (List.replicate terms.length .hole) terms) with
  | node symbol terms children => exact .node .hole symbol terms _ rfl children
  | nil => exact .nil
  | cons term rest first restMatches => exact .cons first restMatches

mutual
  /-- Execute complete-term template matching. -/
  def matchesTerm [DecidableEq Symbol] (pattern : Pattern Symbol) : Term Symbol → Bool
    | .node symbol terms =>
        match childTemplates pattern symbol terms.length with
        | none => false
        | some patterns => matchesChildren patterns terms

  /-- Execute pointwise matching of aligned children. -/
  def matchesChildren [DecidableEq Symbol] : List (Pattern Symbol) → List (Term Symbol) → Bool
    | [], [] => true
    | pattern :: patterns, term :: terms => matchesTerm pattern term && matchesChildren patterns terms
    | _, _ => false
end

/-- Executable matching decides the complete-term pattern relation. -/
theorem matchesTerm_correct [DecidableEq Symbol] (term : Term Symbol) (pattern : Pattern Symbol) :
    matchesTerm pattern term = true ↔ Matches pattern term := by
  induction term using Term.rec
    (motive_2 := fun (terms : List (Term Symbol)) => ∀ patterns : List (Pattern Symbol),
      matchesChildren patterns terms = true ↔ All₂ Matches patterns terms) generalizing pattern with
  | node symbol terms ih =>
      cases aligned : childTemplates pattern symbol terms.length with
      | none =>
          simp only [matchesTerm, aligned, Bool.false_eq_true, false_iff]
          intro matched
          cases matched with
          | node _ _ _ patterns present children => simp [aligned] at present
      | some patterns =>
          simp only [matchesTerm, aligned, ih]
          constructor
          · exact Matches.node pattern symbol terms patterns aligned
          · intro matched
            cases matched with
            | node _ _ _ found present children =>
                have same : patterns = found := by simpa [aligned] using present
                simpa [same] using children
  | nil patterns =>
      cases patterns with
      | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
      | cons pattern patterns =>
          constructor
          · simp [matchesChildren]
          · intro impossible; cases impossible
  | cons term terms first rest patterns =>
      cases patterns with
      | nil =>
          constructor
          · simp [matchesChildren]
          · intro impossible; cases impossible
      | cons pattern patterns =>
          simp only [matchesChildren, Bool.and_eq_true, first, rest]
          exact ⟨fun ⟨head, tail⟩ => .cons head tail,
            fun matched => by cases matched with | cons head tail => exact ⟨head, tail⟩⟩

/-- Restrict one transition by aligning its child templates. -/
def restrictEdge [DecidableEq Symbol] (pattern : Pattern Symbol) (edge : Edge State Symbol) :
    List (Edge (State × Pattern Symbol) Symbol) :=
  match childTemplates pattern edge.label edge.children.length with
  | none => []
  | some patterns => [⟨edge.label, edge.children.zip patterns, edge.guard⟩]

/-- The explicit-state product used by `restrictFTA`. -/
def restrict [DecidableEq Symbol] (automaton : Automaton State Symbol) :
    Automaton (State × Pattern Symbol) Symbol :=
  fun (state, pattern) => (automaton state).flatMap (restrictEdge pattern)

/-- A restricted edge comes from a matching source edge with the original guard. -/
theorem mem_restrict_iff [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (pattern : Pattern Symbol) (edge : Edge (State × Pattern Symbol) Symbol) :
    edge ∈ restrict automaton (state, pattern) ↔
      ∃ source, source ∈ automaton state ∧ ∃ patterns,
        childTemplates pattern source.label source.children.length = some patterns ∧
        edge = ⟨source.label, source.children.zip patterns, source.guard⟩ := by
  simp only [restrict, List.mem_flatMap]
  constructor
  · rintro ⟨source, present, matched⟩
    unfold restrictEdge at matched
    cases aligned : childTemplates pattern source.label source.children.length with
    | none => simp [aligned] at matched
    | some patterns =>
        exact ⟨source, present, patterns, aligned, by simpa [aligned] using matched⟩
  · rintro ⟨source, present, patterns, aligned, rfl⟩
    exact ⟨source, present, by simp [restrictEdge, aligned]⟩

/-- Restricted acceptance preserves source acceptance and establishes the template. -/
theorem restrict_sound [DecidableEq Symbol] (automaton : Automaton State Symbol)
    {pair : State × Pattern Symbol} {term : Term Symbol}
    (accepted : Accepts (restrict automaton) pair term) :
    Accepts automaton pair.1 term ∧ Matches pair.2 term := by
  induction accepted using Accepts.rec
    (motive_2 := fun pairs terms _ => All₂
      (fun (pair : State × Pattern Symbol) term =>
        Accepts automaton pair.1 term ∧ Matches pair.2 term) pairs terms) with
  | @node pair edge terms present children guard ih =>
      obtain ⟨source, sourceMember, patterns, aligned, same⟩ :=
        (mem_restrict_iff automaton pair.1 pair.2 edge).mp present
      subst edge
      have lengthEq := (childTemplates_length pair.2 source.label source.children.length patterns aligned).symm
      have parts := (all₂_zip_iff (Accepts automaton) Matches _ _ _ lengthEq).mp ih
      refine ⟨.node source terms sourceMember parts.1 guard,
        .node pair.2 source.label terms patterns ?_ parts.2⟩
      simpa [← parts.1.length_eq] using aligned
  | nil => exact .nil
  | cons first rest firstProof restProof => exact .cons firstProof restProof

/-- Every source term that matches the template has a restricted accepting run. -/
theorem restrict_complete [DecidableEq Symbol] (automaton : Automaton State Symbol)
    {state : State} {term : Term Symbol} (accepted : Accepts automaton state term) :
    ∀ pattern, Matches pattern term → Accepts (restrict automaton) (state, pattern) term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => ∀ patterns, All₂ Matches patterns terms →
      All₂ (Accepts (restrict automaton)) (states.zip patterns) terms) with
  | @node state source terms present children guard ih =>
      intro pattern matched
      cases matched with
      | node _ _ _ patterns aligned matchedChildren =>
          have edgeAligned : childTemplates pattern source.label source.children.length = some patterns := by
            simpa [children.length_eq] using aligned
          let edge : Edge (State × Pattern Symbol) Symbol :=
            ⟨source.label, source.children.zip patterns, source.guard⟩
          exact .node edge terms
            ((mem_restrict_iff automaton state pattern edge).mpr
              ⟨source, present, patterns, edgeAligned, rfl⟩)
            (ih patterns matchedChildren) guard
  | nil patterns matched => cases matched; exact .nil
  | cons first rest firstProof restProof patterns matched =>
      cases matched with
      | cons head tail => exact .cons (firstProof _ head) (restProof _ tail)

/-- Template restriction retains exactly the accepted terms that match. -/
theorem restrict_exact [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (pattern : Pattern Symbol) (term : Term Symbol) :
    Accepts (restrict automaton) (state, pattern) term ↔
      Accepts automaton state term ∧ Matches pattern term := by
  exact ⟨restrict_sound automaton, fun ⟨accepted, matched⟩ => restrict_complete automaton accepted pattern matched⟩

/-- The hole shortcut preserves the whole accepted language. -/
theorem restrict_hole [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (term : Term Symbol) :
    Accepts (restrict automaton) (state, .hole) term ↔ Accepts automaton state term := by
  rw [restrict_exact]
  exact ⟨And.left, fun accepted => ⟨accepted, hole_matches term⟩⟩

end MicroCFTA.Template
