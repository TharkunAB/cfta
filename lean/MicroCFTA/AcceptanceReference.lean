import MicroCFTA.NumberedTerms

/-!
# Direct ordered acceptance

This model follows `Internal.Tree.acceptsBy` matching, ordered alternatives,
and ordered child checks. Guards are stable Boolean predicates of the state,
alternative, and complete term. The height parameter bounds structural
recursion, including when the automaton itself contains cycles.
-/

namespace MicroCFTA.AcceptanceReference
open Language

/-- Match both the root symbol and exact child count before any recursive check. -/
def matchesRoot [DecidableEq Symbol] (edge : Edge State Symbol) : Term Symbol → Bool
  | .node symbol children => decide (edge.label = symbol) && decide (edge.children.length = children.length)

/-- The source's zip-based child conjunction, evaluated from left to right. -/
def zipAll (check : α → β → Bool) : List α → List β → Bool
  | [], _ | _, [] => true
  | key :: keys, term :: terms => check key term && zipAll check keys terms

/-- Exact arity makes zip-based checking equivalent to a complete pointwise child relation. -/
theorem zipAll_correct (check : α → β → Bool) (keys : List α) (terms : List β)
    (arity : keys.length = terms.length) :
    zipAll check keys terms = true ↔ All₂ (fun key term => check key term = true) keys terms := by
  induction keys generalizing terms with
  | nil =>
      have empty : terms = [] := List.length_eq_zero_iff.mp arity.symm
      subst terms
      exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons key keys ih =>
      cases terms with
      | nil => simp at arity
      | cons term terms =>
          have same : keys.length = terms.length := by simpa using arity
          constructor
          · intro accepted
            have parts := Bool.and_eq_true_iff.mp accepted
            exact .cons parts.1 ((ih terms same).mp parts.2)
          · intro accepted
            cases accepted with
            | cons first rest => exact Bool.and_eq_true_iff.mpr ⟨first, (ih terms same).mpr rest⟩

/-- Direct ordered search tries guards only after matching and successful children. -/
def accept [DecidableEq Symbol] (automaton : Automaton State Symbol) : Nat → State → Term Symbol → Bool
  | 0, _, _ => false
  | fuel + 1, key, term@(.node _ children) =>
      (automaton key).any fun edge => matchesRoot edge term &&
        (zipAll (accept automaton fuel) edge.children children && edge.guard term)

/-- The direct search returns true exactly for a bounded accepting derivation. -/
theorem accept_exact [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (fuel : Nat) (key : State) (term : Term Symbol) :
    accept automaton fuel key term = true ↔ Accepts automaton key term ∧ term.height ≤ fuel := by
  induction fuel generalizing key term with
  | zero =>
      have positive := term.height_pos
      simp [accept, show ¬term.height ≤ 0 by omega]
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          simp only [accept, List.any_eq_true, Bool.and_eq_true_iff, matchesRoot, decide_eq_true_eq]
          constructor
          · rintro ⟨edge, member, ⟨symbolMatches, arity⟩, childrenAccepted, guard⟩
            have paired := (zipAll_correct (accept automaton fuel) edge.children children arity).mp childrenAccepted
            have bounded := paired.imp (fun q t h => (ih q t).mp h)
            have parts := (all₂_height_iff (Accepts automaton) edge.children children fuel).mp bounded
            exact ⟨(accepts_node_iff automaton key symbol children).mpr ⟨edge, member, symbolMatches, parts.1, guard⟩,
              by simpa [Term.height, forestHeight] using Nat.succ_le_succ parts.2⟩
          · rintro ⟨accepted, height⟩
            obtain ⟨edge, member, symbolMatches, childrenAccepted, guard⟩ := (accepts_node_iff automaton key symbol children).mp accepted
            have forestBound : forestHeight children ≤ fuel := by simpa [Term.height, forestHeight] using height
            have bounded := (all₂_height_iff (Accepts automaton) edge.children children fuel).mpr ⟨childrenAccepted, forestBound⟩
            have checked := bounded.imp (fun q t h => (ih q t).mpr h)
            exact ⟨edge, member, ⟨symbolMatches, childrenAccepted.length_eq⟩,
              (zipAll_correct (accept automaton fuel) edge.children children childrenAccepted.length_eq).mpr checked, guard⟩

/-- Sufficient structural fuel gives exact acceptance with no graph-acyclicity premise. -/
theorem accept_complete [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (fuel : Nat) (key : State) (term : Term Symbol) (enough : term.height ≤ fuel) :
    accept automaton fuel key term = true ↔ Accepts automaton key term := by
  rw [accept_exact]
  simp [enough]

/-- Source `fromMatch` retains the list starting at the first matching alternative. -/
def fromMatch [DecidableEq Symbol] (term : Term Symbol) : List (Edge State Symbol) → List (Edge State Symbol)
  | [] => []
  | edge :: rest => if matchesRoot edge term then edge :: rest else fromMatch term rest

/-- Skipping the unmatched prefix leaves exactly the same ordered matching alternatives. -/
theorem fromMatch_filter [DecidableEq Symbol] (term : Term Symbol) (edges : List (Edge State Symbol)) :
    (fromMatch term edges).filter (fun edge => matchesRoot edge term) = edges.filter (fun edge => matchesRoot edge term) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih => cases matching : matchesRoot edge term <;> simp [fromMatch, matching, ih]

/-- An empty first-match result means that no alternative matches the term. -/
theorem fromMatch_empty [DecidableEq Symbol] (term : Term Symbol) (edges : List (Edge State Symbol)) :
    fromMatch term edges = [] ↔ ∀ edge ∈ edges, matchesRoot edge term = false := by
  induction edges with
  | nil => simp [fromMatch]
  | cons edge rest ih => cases matching : matchesRoot edge term <;> simp [fromMatch, matching, ih]

end MicroCFTA.AcceptanceReference
