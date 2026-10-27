import MicroCFTA.SourcePruningPartialMatch

/-!
# Complete-term meaning of actual partial matches

A raw hole denotes its assigned complete term.
Truncation permits every complete term.
Successful matching preserves the template when each pending part matches.
-/
namespace MicroCFTA.SourcePruningPartialMatch
open Language EnumerationState

/-- Replace raw holes by their assignment and retain each concrete constructor. -/
inductive Completes (assignment : Nat → Term Symbol) : Term (PartialSymbol Symbol) → Term Symbol → Prop where
  /-- Concrete nodes retain their symbol and ordered completed children. -/
  | concrete (symbol : Symbol) (partials : List (Term (PartialSymbol Symbol))) (terms : List (Term Symbol))
      (children : All₂ (Completes assignment) partials terms) :
      Completes assignment (.node (.concrete symbol) partials) (.node symbol terms)
  /-- A raw hole denotes the assigned term at its original variable. -/
  | hole (uv : Nat) : Completes assignment (.node (.hole uv) []) (assignment uv)
  /-- Truncation imposes no condition on the complete term. -/
  | truncated (partials : List (Term (PartialSymbol Symbol))) (term : Term Symbol) :
      Completes assignment (.node .truncated partials) term

variable [DecidableEq Symbol]

private theorem holes_match (terms : List (Term Symbol)) :
    All₂ Template.Matches (List.replicate terms.length .hole) terms := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (Template.hole_matches term) ih

private theorem empty_prefix_matches (term : Term Symbol) : Template.Matches (.anyPrefix []) term := by
  cases term with
  | node symbol terms =>
      exact .node (.anyPrefix []) symbol terms _
        (by simp [Template.childTemplates, Template.prefixChildren]) (holes_match terms)

private theorem prefix_cons
    (symbol : Symbol) (pattern : Template.Pattern Symbol) (patterns : List (Template.Pattern Symbol))
    (observedTerm : Term (PartialSymbol Symbol)) (partials : List (Term (PartialSymbol Symbol)))
    (pending : Pending Symbol) (enough : patterns.length ≤ partials.length)
    (matched : matchPartial (.anyPrefix (pattern :: patterns))
      (.node (.concrete symbol) (observedTerm :: partials)) = some pending) :
    ∃ first rest, matchPartial pattern observedTerm = some first ∧
      matchPartial (.anyPrefix patterns) (.node (.concrete symbol) partials) = some rest ∧
      first ++ rest = pending := by
  have whole : (pattern :: patterns).length ≤ (observedTerm :: partials).length := by
    simpa only [List.length_cons] using Nat.succ_le_succ enough
  have combined :
      ((matchPartial pattern observedTerm).bind fun first =>
        (matchPartial (.anyPrefix patterns) (.node (.concrete symbol) partials)).bind fun rest =>
          some (first ++ rest)) = some pending := by
    cases patterns with
    | nil =>
        simp only [matchPartial, ite_eq_left whole] at matched ⊢
        try dsimp! at matched ⊢
        exact matched
    | cons next rest =>
        simp only [matchPartial, ite_eq_left whole, ite_eq_left enough] at matched ⊢
        try dsimp! at matched ⊢
        exact matched
  cases firstFound : matchPartial pattern observedTerm with
  | none => simp only [firstFound, Option.bind_none] at combined; cases combined
  | some first =>
      cases restFound : matchPartial (.anyPrefix patterns) (.node (.concrete symbol) partials) with
      | none => simp only [firstFound, restFound, Option.bind_some, Option.bind_none] at combined; cases combined
      | some rest =>
          refine ⟨first, rest, rfl, rfl, ?_⟩
          exact Option.some.inj (by simpa only [firstFound, restFound, Option.bind_some] using combined)

/-- Actual partial matching is sound for every completion whose pending parts match. -/
theorem matchPartial_sound
    (assignment : Nat → Term Symbol) (pattern : Template.Pattern Symbol)
    (observedTerm : Term (PartialSymbol Symbol)) (full : Term Symbol) (pending : Pending Symbol)
    (completed : Completes assignment observedTerm full)
    (matched : matchPartial pattern observedTerm = some pending)
    (pendingMatches : ∀ entry ∈ pending, Template.Matches entry.1 (assignment entry.2)) :
    Template.Matches pattern full := by
  induction observedTerm using Term.rec
    (motive_2 := fun partials =>
      ∀ (terms : List (Term Symbol)), All₂ (Completes assignment) partials terms →
      ∀ (symbol : Symbol) (patterns : List (Template.Pattern Symbol)) (pending : Pending Symbol),
        patterns.length ≤ partials.length →
        matchPartial (.anyPrefix patterns) (.node (.concrete symbol) partials) = some pending →
        (∀ entry ∈ pending, Template.Matches entry.1 (assignment entry.2)) →
        All₂ Template.Matches (patterns ++ List.replicate (terms.length - patterns.length) .hole) terms)
    generalizing pattern full pending with
  | node partialSymbol partials ih =>
      cases completed with
      | concrete symbol partials terms children =>
          have lengths := children.length_eq
          cases pattern with
          | hole => exact Template.hole_matches _
          | anyNode parts =>
              by_cases same : parts.length = partials.length
              · have enough : parts.length ≤ partials.length := Nat.le_of_eq same
                have prefixMatched : matchPartial (.anyPrefix parts) (.node (.concrete symbol) partials) =
                    some pending := by
                  cases parts <;>
                      simp only [matchPartial, ite_eq_left same, ite_eq_left enough] at matched ⊢ <;>
                      try dsimp! at matched ⊢ <;>
                      exact matched
                have aligned := ih terms children symbol parts pending enough prefixMatched pendingMatches
                have fullLength : parts.length = terms.length := same.trans lengths
                refine .node (.anyNode parts) symbol terms parts ?_ ?_
                · simp only [Template.childTemplates, Template.exactChildren, ite_eq_left fullLength]
                · simpa only [← fullLength, Nat.sub_self, List.replicate_zero, List.append_nil] using aligned
              · simp only [matchPartial, ite_eq_right same] at matched
                cases matched
          | node expected parts =>
              by_cases symbolSame : expected = symbol
              · subst expected
                by_cases same : parts.length = partials.length
                · have enough : parts.length ≤ partials.length := Nat.le_of_eq same
                  have prefixMatched : matchPartial (.anyPrefix parts) (.node (.concrete symbol) partials) =
                      some pending := by
                    cases parts <;>
                      simp only [matchPartial, ↓reduceIte, ite_eq_left same, ite_eq_left enough] at matched ⊢ <;>
                      try dsimp! at matched ⊢ <;>
                      exact matched
                  have aligned := ih terms children symbol parts pending enough prefixMatched pendingMatches
                  have fullLength : parts.length = terms.length := same.trans lengths
                  refine .node (.node symbol parts) symbol terms parts ?_ ?_
                  · simp only [Template.childTemplates, ↓reduceIte, Template.exactChildren, ite_eq_left fullLength]
                  · simpa only [← fullLength, Nat.sub_self, List.replicate_zero, List.append_nil] using aligned
                · simp only [matchPartial, ↓reduceIte, ite_eq_right same] at matched
                  cases matched
              · simp only [matchPartial, ite_eq_right symbolSame] at matched
                cases matched
          | anyPrefix parts =>
              have enough : parts.length ≤ partials.length := by
                cases parts with
                | nil => exact Nat.zero_le _
                | cons part rest =>
                    by_cases enough : (part :: rest).length ≤ partials.length
                    · exact enough
                    · simp only [matchPartial, ite_eq_right enough] at matched
                      cases matched
              have fullEnough : parts.length ≤ terms.length := by omega
              exact .node (.anyPrefix parts) symbol terms _
                (by simp only [Template.childTemplates, Template.prefixChildren, ite_eq_left fullEnough])
                (ih terms children symbol parts pending enough matched pendingMatches)
          | «prefix» expected parts =>
              by_cases symbolSame : expected = symbol
              · subst expected
                by_cases enough : parts.length ≤ partials.length
                · have prefixMatched : matchPartial (.anyPrefix parts) (.node (.concrete symbol) partials) =
                      some pending := by
                    cases parts <;>
                      simp only [matchPartial, ↓reduceIte, ite_eq_left enough] at matched ⊢ <;>
                      try dsimp! at matched ⊢ <;>
                      exact matched
                  have fullEnough : parts.length ≤ terms.length := by omega
                  exact .node (.«prefix» symbol parts) symbol terms _
                    (by simp only [Template.childTemplates, ↓reduceIte, Template.prefixChildren, ite_eq_left fullEnough])
                    (ih terms children symbol parts pending enough prefixMatched pendingMatches)
                · simp only [matchPartial, ↓reduceIte, ite_eq_right enough] at matched
                  cases matched
              · simp only [matchPartial, ite_eq_right symbolSame] at matched
                cases matched
      | hole uv =>
          rw [matchPartial_rawHole] at matched
          cases pattern with
          | hole => exact Template.hole_matches _
          | anyNode parts | node symbol parts | «prefix» symbol parts =>
              have same := Option.some.inj matched
              rw [← same] at pendingMatches
              exact pendingMatches _ (List.mem_singleton_self _)
          | anyPrefix parts =>
              cases parts with
              | nil => exact empty_prefix_matches _
              | cons part rest =>
                  have same := Option.some.inj matched
                  rw [← same] at pendingMatches
                  exact pendingMatches _ (List.mem_singleton_self _)
      | truncated partials term =>
          rw [matchPartial_truncated] at matched
          cases pattern with
          | hole => exact Template.hole_matches _
          | anyNode _ | node _ _ | «prefix» _ _ => cases matched
          | anyPrefix parts =>
              cases parts with
              | nil => exact empty_prefix_matches _
              | cons _ _ => cases matched
  | nil =>
      rename_i terms children symbol patterns pending enough _matched _pendingMatches
      cases children
      have empty : patterns = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
      subst patterns
      exact .nil
  | cons observedTerm partials first rest =>
      rename_i terms children symbol patterns pending enough matched pendingMatches
      cases children with
      | @cons _ term _ terms childCompleted restCompleted =>
          cases patterns with
          | nil =>
              simpa only [List.nil_append, List.length_nil, Nat.sub_zero] using holes_match (term :: terms)
          | cons pattern patterns =>
              have tailEnough : patterns.length ≤ partials.length := by
                simpa only [List.length_cons] using Nat.le_of_succ_le_succ enough
              obtain ⟨firstPending, restPending, firstMatch, restMatch, same⟩ :=
                prefix_cons symbol pattern patterns observedTerm partials pending tailEnough matched
              have firstMatched := first pattern term firstPending childCompleted firstMatch (by
                intro entry member
                apply pendingMatches entry
                rw [← same]
                exact List.mem_append_left _ member)
              have restMatched := rest terms restCompleted symbol patterns restPending tailEnough restMatch (by
                intro entry member
                apply pendingMatches entry
                rw [← same]
                exact List.mem_append_right _ member)
              simpa only [List.cons_append, List.length_cons, Nat.add_sub_add_right] using
                (All₂.cons firstMatched restMatched)

/-- An actual complete partial match needs no pending semantic assumption. -/
theorem matchPartial_complete_sound
    (assignment : Nat → Term Symbol) (pattern : Template.Pattern Symbol)
    (observedTerm : Term (PartialSymbol Symbol)) (full : Term Symbol)
    (completed : Completes assignment observedTerm full)
    (matched : matchPartial pattern observedTerm = some []) : Template.Matches pattern full := by
  exact matchPartial_sound assignment pattern observedTerm full [] completed matched (by simp)

/-- A refuted original template leaves a refutable group in every actual partial match. -/
theorem matchPartial_refutes
    (assignment : Nat → Term Symbol) (pattern : Template.Pattern Symbol)
    (observedTerm : Term (PartialSymbol Symbol)) (full : Term Symbol) (pending : Pending Symbol)
    (completed : Completes assignment observedTerm full)
    (matched : matchPartial pattern observedTerm = some pending)
    (refuted : ¬ Template.Matches pattern full) :
    ¬ (∀ entry ∈ pending, Template.Matches entry.1 (assignment entry.2)) := by
  intro allMatch
  exact refuted (matchPartial_sound assignment pattern observedTerm full pending completed matched allMatch)

end MicroCFTA.SourcePruningPartialMatch
