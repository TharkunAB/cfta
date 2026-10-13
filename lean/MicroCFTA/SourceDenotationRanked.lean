import MicroCFTA.SourceDenotationLiquid
import MicroCFTA.SourceFromTermsArity

/-!
# Ranked-alphabet consequence of exact denotation

A denotation list from a ranked source automaton has one child count for
every symbol in all of its subterms. The actual finite-term constructor can
therefore rebuild it without an arity-validation failure.
-/

namespace MicroCFTA.SourceDenotationRanked

open Language

/-- Every subterm of an accepted tree has the source alphabet's declared arity. -/
theorem accepted_subterms (automaton : Automaton State Symbol) (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    {state term} (accepted : Accepts automaton state term) :
    ∀ symbol children, Term.node symbol children ∈ FromTerms.subterms term → assignment symbol = children.length := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => ∀ term ∈ terms, ∀ symbol children,
      Term.node symbol children ∈ FromTerms.subterms term → assignment symbol = children.length) with
  | @node state edge children member runs guard ih =>
      intro symbol nested present
      simp only [FromTerms.subterms] at present
      rcases List.mem_cons.mp present with same | below
      · cases same
        exact (ranked state edge member).trans runs.length_eq
      · obtain ⟨child, childIn, nestedIn⟩ := List.mem_flatMap.mp below
        exact ih child childIn symbol nested nestedIn
  | nil => simp_all
  | cons head tail ihHead ihTail =>
      rename_i term member symbol children nested
      rcases List.mem_cons.mp member with rfl | present
      · exact ihHead symbol children nested
      · exact ihTail term present symbol children nested

/-- Accepted output from one ranked source gives the exact input contract of the finite rebuild. -/
theorem output_ranked (automaton : Automaton State Symbol) (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    (output : List (Term Symbol))
    (sound : ∀ term ∈ output, ∃ state, Accepts automaton state term) :
    SourceFromTerms.Ranked output assignment := by
  intro symbol children present
  obtain ⟨term, member, nested⟩ := List.mem_flatMap.mp present
  obtain ⟨state, accepted⟩ := sound term member
  exact accepted_subterms automaton assignment ranked accepted symbol children nested

/-- Finite rebuild cannot reject any successful denotation over a ranked source alphabet. -/
theorem rebuild_succeeds [DecidableEq Symbol] [Ord (Term Symbol)] [Ord (Option (Term Symbol))]
    (automaton : Automaton State Symbol) (assignment : Symbol → Nat)
    (ranked : ∀ state edge, edge ∈ automaton state → assignment edge.label = edge.children.length)
    (output : List (Term Symbol))
    (sound : ∀ term ∈ output, ∃ state, Accepts automaton state term) :
    SourceFromTerms.build output = .ok (FTAValidation.normalizeRows (SourceFromTerms.rows output)) :=
  (SourceFromTerms.build_ok_iff output).mpr ⟨assignment, output_ranked automaton assignment ranked output sound⟩

end MicroCFTA.SourceDenotationRanked
