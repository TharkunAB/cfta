import MicroCFTA.Template
import MicroCFTA.EnumerationState
import MicroCFTA.EnumerationPartialBounds

/-!
# Pure matching of partial pruning terms

The branch order follows Specftacular.Pruning.matchPartial.
Pending entries retain their pattern and original hole ID in child order.
-/
namespace MicroCFTA.SourcePruningPartialMatch

/-- The unresolved pieces of one template match. -/
abbrev Pending (Symbol : Type) := List (Template.Pattern Symbol × Nat)

/-- Every parked match names an allocated variable. -/
def PendingBound (limit : Nat) (pending : Pending Symbol) : Prop :=
  ∀ entry ∈ pending, entry.2 < limit

mutual
  /-- Match a partial term and collect the unresolved pieces in order. -/
  def matchPartial [DecidableEq Symbol] (pattern : Template.Pattern Symbol)
      (term : Language.Term (EnumerationState.PartialSymbol Symbol)) : Option (Pending Symbol) :=
    match pattern, term with
    | .hole, _ => some []
    | .anyPrefix [], _ => some []
    | pattern, .node (.hole uv) [] => some [(pattern, uv)]
    | _, .node .truncated _ => none
    | .anyNode parts, .node (.concrete _) children =>
        if parts.length = children.length then matchChildren parts children else none
    | .node expected parts, .node (.concrete symbol) children =>
        if expected = symbol then
          if parts.length = children.length then matchChildren parts children else none
        else none
    | .anyPrefix parts, .node (.concrete _) children =>
        if parts.length ≤ children.length then matchChildren parts children else none
    | .prefix expected parts, .node (.concrete symbol) children =>
        if expected = symbol then
          if parts.length ≤ children.length then matchChildren parts children else none
        else none
    | _, _ => none

  /-- Match the requested prefix and append each child's pending pieces. -/
  private def matchChildren [DecidableEq Symbol] : List (Template.Pattern Symbol) →
      List (Language.Term (EnumerationState.PartialSymbol Symbol)) → Option (Pending Symbol)
    | [], _ => some []
    | pattern :: patterns, term :: terms => do
        let first ← matchPartial pattern term
        let rest ← matchChildren patterns terms
        pure (first ++ rest)
    | _, [] => none
end

/-- A hole pattern accepts every partial shape without a pending piece. -/
theorem matchPartial_hole [DecidableEq Symbol]
    (term : Language.Term (EnumerationState.PartialSymbol Symbol)) :
    matchPartial .hole term = some [] := by
  rfl

/-- The empty unrestricted prefix accepts even holes and truncation. -/
theorem matchPartial_anyPrefix_nil [DecidableEq Symbol]
    (term : Language.Term (EnumerationState.PartialSymbol Symbol)) :
    matchPartial (.anyPrefix []) term = some [] := by
  rfl

/-- A raw hole suspends the exact pattern unless a wildcard already accepts it. -/
theorem matchPartial_rawHole [DecidableEq Symbol] (pattern : Template.Pattern Symbol) (uv : Nat) :
    matchPartial pattern (.node (.hole uv) []) =
      match pattern with
      | .hole => some []
      | .anyPrefix [] => some []
      | _ => some [(pattern, uv)] := by
  cases pattern with
  | hole => rfl
  | anyNode parts => rfl
  | node symbol parts => rfl
  | anyPrefix parts => cases parts <;> rfl
  | «prefix» symbol parts => rfl

/-- Truncation rejects every pattern except the two preceding wildcards. -/
theorem matchPartial_truncated [DecidableEq Symbol] (pattern : Template.Pattern Symbol)
    (children : List (Language.Term (EnumerationState.PartialSymbol Symbol))) :
    matchPartial pattern (.node .truncated children) =
      match pattern with
      | .hole => some []
      | .anyPrefix [] => some []
      | _ => none := by
  cases pattern with
  | hole => rfl
  | anyNode parts => rfl
  | node symbol parts => rfl
  | anyPrefix parts => cases parts <;> rfl
  | «prefix» symbol parts => rfl

/-- A successful partial match parks only holes from the bounded input term. -/
theorem matchPartial_bounded [DecidableEq Symbol] (limit : Nat)
    (pattern : Template.Pattern Symbol) (term : Language.Term (EnumerationState.PartialSymbol Symbol))
    (pending : Pending Symbol) (bounded : EnumerationPartialBounds.TermBound limit term)
    (matched : matchPartial pattern term = some pending) : PendingBound limit pending := by
  induction term using Language.Term.rec
    (motive_2 := fun children => ∀ (patterns : List (Template.Pattern Symbol)) (pending : Pending Symbol),
      EnumerationPartialBounds.TermsBound limit children →
      matchChildren patterns children = some pending → PendingBound limit pending)
    generalizing pattern pending with
  | node symbol children ih =>
      cases symbol with
      | concrete symbol =>
          cases pattern with
          | hole => simp_all [matchPartial, PendingBound]
          | anyNode parts =>
              simp only [matchPartial] at matched
              split at matched
              · exact ih parts pending bounded.2 matched
              · cases matched
          | node expected parts =>
              simp only [matchPartial] at matched
              split at matched
              · split at matched
                · exact ih parts pending bounded.2 matched
                · cases matched
              · cases matched
          | anyPrefix parts =>
              cases parts with
              | nil => simp_all [matchPartial, PendingBound]
              | cons part parts =>
                  simp only [matchPartial] at matched
                  split at matched
                  · exact ih (part :: parts) pending bounded.2 matched
                  · cases matched
          | «prefix» expected parts =>
              simp only [matchPartial] at matched
              split at matched
              · split at matched
                · exact ih parts pending bounded.2 matched
                · cases matched
              · cases matched
      | hole uv =>
          cases children <;> cases pattern with
          | anyPrefix parts =>
              cases parts <;> simp_all [matchPartial, PendingBound,
                EnumerationPartialBounds.TermBound, EnumerationPartialBounds.TermsBound]
          | hole | anyNode _ | node _ _ | «prefix» _ _ =>
              simp_all [matchPartial, PendingBound,
                EnumerationPartialBounds.TermBound, EnumerationPartialBounds.TermsBound]
      | truncated =>
          cases pattern with
          | anyPrefix parts => cases parts <;> simp_all [matchPartial, PendingBound]
          | hole | anyNode _ | node _ _ | «prefix» _ _ => simp_all [matchPartial, PendingBound]
  | nil =>
      intro patterns pending _bounded matched
      cases patterns <;> simp_all [matchChildren, PendingBound]
  | cons child children first rest =>
      intro patterns pending bounded matched
      cases patterns with
      | nil => simp_all [matchChildren, PendingBound]
      | cons pattern patterns =>
          cases firstFound : matchPartial pattern child with
          | none => simp [matchChildren, firstFound] at matched
          | some firstPending =>
              cases restFound : matchChildren patterns children with
              | none => simp [matchChildren, firstFound, restFound] at matched
              | some restPending =>
                  have same : firstPending ++ restPending = pending := by
                    simpa [matchChildren, firstFound, restFound] using matched
                  rw [← same]
                  intro entry member
                  rcases List.mem_append.mp member with inFirst | inRest
                  · exact first pattern firstPending bounded.1 firstFound entry inFirst
                  · exact rest patterns restPending bounded.2 restFound entry inRest

end MicroCFTA.SourcePruningPartialMatch
