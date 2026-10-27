import MicroCFTA.Template

/-!
# Template absence at every term position

The Boolean workers follow matchesNone and matchesNowhere in the source.
The specification uses independent subterm lookup and template matching.
These predicates do not establish correctness of obligationRows or fromRows.
-/
namespace MicroCFTA.SourceTemplateAnywhere
open Language Template

/-- Reject a root when one of the given templates matches it. -/
def matchesNone [DecidableEq Symbol] (templates : List (Pattern Symbol)) (term : Term Symbol) : Bool :=
  !(templates.any (fun pattern => matchesTerm pattern term))

/-- Root rejection agrees with independent template matching. -/
theorem matchesNone_correct [DecidableEq Symbol] (templates : List (Pattern Symbol)) (term : Term Symbol) :
    matchesNone templates term = true ↔ ∀ pattern ∈ templates, ¬Matches pattern term := by
  simp only [matchesNone, Bool.not_eq_true', List.any_eq_false, matchesTerm_correct]

mutual
/-- Check the root before checking each child in source order. -/
def matchesNowhere [DecidableEq Symbol] (templates : List (Pattern Symbol)) : Term Symbol → Bool
  | .node symbol children => matchesNone templates (.node symbol children) && matchesChildrenNowhere templates children

/-- Check each complete child and then the remaining children. -/
def matchesChildrenNowhere [DecidableEq Symbol] (templates : List (Pattern Symbol)) : List (Term Symbol) → Bool
  | [] => true
  | first :: rest => matchesNowhere templates first && matchesChildrenNowhere templates rest
end

/-- The ordered child worker equals the source list predicate. -/
theorem children_eq_all [DecidableEq Symbol] (templates : List (Pattern Symbol)) (children : List (Term Symbol)) :
    matchesChildrenNowhere templates children = children.all (matchesNowhere templates) := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [matchesChildrenNowhere, List.all_cons, ih]

/-- The complete term worker has the literal source root-and-children equation. -/
theorem matchesNowhere_equation [DecidableEq Symbol] (templates : List (Pattern Symbol))
    (symbol : Symbol) (children : List (Term Symbol)) :
    matchesNowhere templates (.node symbol children) =
      (matchesNone templates (.node symbol children) && children.all (matchesNowhere templates)) := by
  simp only [matchesNowhere, children_eq_all]

/-- No existing subterm matches any of the given templates. -/
def NoMatchAt [DecidableEq Symbol] (templates : List (Pattern Symbol)) (term : Term Symbol) : Prop :=
  ∀ path subtree, term.atPath path = some subtree → ∀ pattern ∈ templates, ¬Matches pattern subtree

/-- The source worker rejects exactly the terms with a matching existing subterm. -/
theorem matchesNowhere_correct [DecidableEq Symbol] (templates : List (Pattern Symbol)) (term : Term Symbol) :
    matchesNowhere templates term = true ↔ NoMatchAt templates term := by
  induction term using Term.rec
    (motive_2 := fun terms : List (Term Symbol) =>
      matchesChildrenNowhere templates terms = true ↔ ∀ child ∈ terms, NoMatchAt templates child) with
  | node symbol children ih =>
      simp only [matchesNowhere, Bool.and_eq_true, matchesNone_correct, ih]
      constructor
      · rintro ⟨root, descendants⟩ path subtree found pattern member
        cases path with
        | nil =>
            have same := Option.some.inj found
            subst subtree
            exact root pattern member
        | cons index rest =>
            cases selected : children[index]? with
            | none => simp only [Term.atPath, selected, Option.bind_none] at found; cases found
            | some child =>
                have below : child.atPath rest = some subtree := by
                  simpa only [Term.atPath, selected, Option.bind_some] using found
                exact descendants child (List.mem_of_getElem? selected) rest subtree below pattern member
      · intro absent
        refine ⟨absent [] (.node symbol children) rfl, ?_⟩
        intro child member path subtree found pattern present
        obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
        have below : (Term.node symbol children).atPath (index :: path) = some subtree := by
          simpa only [Term.atPath, selected, Option.bind_some] using found
        exact absent (index :: path) subtree below pattern present
  | nil => simp [matchesChildrenNowhere]
  | cons first rest head tail =>
      simp only [matchesChildrenNowhere, Bool.and_eq_true, head, tail]
      constructor
      · rintro ⟨own, others⟩ child member
        rcases List.mem_cons.mp member with rfl | later
        · exact own
        · exact others child later
      · intro all
        exact ⟨all first List.mem_cons_self, fun child member => all child (List.mem_cons_of_mem _ member)⟩

/-- Every selected existing subterm retains the source absence predicate. -/
theorem matchesNowhere_subterm [DecidableEq Symbol] (templates : List (Pattern Symbol))
    (term subtree : Term Symbol) (path : List Nat) (found : term.atPath path = some subtree)
    (absent : matchesNowhere templates term = true) : matchesNowhere templates subtree = true := by
  apply (matchesNowhere_correct templates subtree).mpr
  intro below selected lookup pattern member
  have combined : term.atPath (path ++ below) = some selected := by
    simpa only [atPath_append, found, Option.bind_some] using lookup
  exact (matchesNowhere_correct templates term).mp absent (path ++ below) selected combined pattern member

/-- A hole in the forbidden templates rejects every complete term. -/
theorem hole_rejects [DecidableEq Symbol] (templates : List (Pattern Symbol)) (term : Term Symbol)
    (present : .hole ∈ templates) : matchesNowhere templates term = false := by
  cases actual : matchesNowhere templates term with
  | false => rfl
  | true =>
      have absent := (matchesNowhere_correct templates term).mp actual
      exact False.elim (absent [] term rfl .hole present (hole_matches term))

end MicroCFTA.SourceTemplateAnywhere
