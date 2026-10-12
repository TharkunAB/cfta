import MicroCFTA.EnumerationExact

/-!
# Finite height bounds for complete enumeration

The complete graph view maps to the existing guarded language interpreter.
Its finite height-bounded list gives one sufficient driver bound for all terms
at that height, rather than a separate bound for each term.
-/

namespace MicroCFTA.EnumerationLanguage
open Language EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationConstruction EnumerationAssignment EnumerationExecution EnumerationExact

/-- A graph edge combines its equality classes and residual predicate into one guard. -/
noncomputable def edgeView (meaning : Guard → Term Symbol → Prop) (edge : EnumerationState.Edge Symbol Guard) : Language.Edge Nat Symbol := by
  classical
  exact ⟨edge.symbol, edge.children, fun term => decide ((∀ trie ∈ edge.equalities, EqualityHolds term trie) ∧ ResidualHolds meaning edge.residual term)⟩

/-- The complete graph view supplies the finite outgoing list used by the guarded interpreter. -/
noncomputable def automaton (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) : Automaton Nat Symbol :=
  fun node => match graph.node node with | .alternatives edges => edges.map (edgeView meaning) | _ => []

/-- The graph view and the guarded language interpreter have the same finite acceptance. -/
theorem accepted_iff (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) (complete : CompleteGraph graph)
    (node : Nat) (term : Term Symbol) : Accepted graph meaning node term ↔ Accepts (automaton graph meaning) node term := by
  classical
  have equivalent : ∀ height, ∀ node term, term.height = height →
      (Accepted graph meaning node term ↔ Accepts (automaton graph meaning) node term) := by
    intro height
    induction height using Nat.strongRecOn with
    | ind height ih =>
        intro node term heightEq
        constructor
        · intro accepted
          cases accepted with
          | recursive node body term view inside => exact (complete.1 node body view).elim
          | edge node edges edge children view member accepted equalities residual =>
              apply Accepts.node (edgeView meaning edge) children
              · simp only [automaton, view]
                exact List.mem_map.mpr ⟨edge, member, rfl⟩
              · apply all₂_imp_mem edge.children children (Accepted graph meaning) _ accepted
                intro childNode child member proof
                have small := height_le_forestHeight children child member
                have bound : child.height < height := by
                  rw [← heightEq]
                  simp only [Term.height]
                  unfold forestHeight at small
                  omega
                exact (ih child.height bound childNode child rfl).mp proof
              · simpa [edgeView] using And.intro equalities residual
        · intro accepted
          cases accepted with
          | node converted children member childAccepted guard =>
              cases view : graph.node node with
              | empty | recursive _ | unresolved _ => simp [automaton, view] at member
              | alternatives edges =>
                  simp only [automaton, view] at member
                  obtain ⟨edge, listed, convertedSame⟩ := List.mem_map.mp member
                  subst converted
                  have constraints : (∀ trie ∈ edge.equalities, EqualityHolds (.node edge.symbol children) trie) ∧
                      ResidualHolds meaning edge.residual (.node edge.symbol children) := by simpa [edgeView] using guard
                  apply Accepted.edge node edges edge children view listed
                  · apply all₂_imp_mem edge.children children (Accepts (automaton graph meaning)) _ childAccepted
                    intro childNode child member proof
                    have small := height_le_forestHeight children child member
                    have bound : child.height < height := by
                      rw [← heightEq]
                      simp only [edgeView, Term.height]
                      unfold forestHeight at small
                      omega
                    exact (ih child.height bound childNode child rfl).mpr proof
                  · exact constraints.1
                  · exact constraints.2
  exact equivalent term.height node term rfl

/-- The finite guarded list contains exactly the graph's accepted terms within its height bound. -/
theorem bounded_terms_exact (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop) (complete : CompleteGraph graph)
    (height node : Nat) (term : Term Symbol) :
    term ∈ Language.enumerate (automaton graph meaning) height node ↔ Accepted graph meaning node term ∧ term.height ≤ height := by
  rw [Language.mem_enumerate_iff, ← accepted_iff graph meaning complete]

/-- A finite list of accepted terms has one driver bound that retains every listed term. -/
theorem finite_uniform_bound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (root : Nat) (terms : List (Term Symbol)) (accepted : ∀ term ∈ terms, Accepted graph meaning root term) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ term ∈ terms, ∃ pending after, .ok ((term, pending), after) ∈ runs graph marker fuel root ∧
      ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
  induction terms with
  | nil => exact ⟨0, by simp⟩
  | cons term rest ih =>
      obtain ⟨firstBound, pending, after, first, checked⟩ := runs_complete_eventually graph meaning complete correct marker root term (accepted term (by simp))
      obtain ⟨restBound, remaining⟩ := ih (fun term member => accepted term (by simp [member]))
      refine ⟨max firstBound restBound, ?_⟩
      intro fuel enough output member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨pending, after, first fuel (by omega), checked⟩
      · exact remaining fuel (by omega) output member

/-- Every fixed term-height bound has one sufficient execution bound for all its accepted terms. -/
theorem runs_uniform_height_bound (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (root height : Nat) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ term, term.height ≤ height →
      (Accepted graph meaning root term ↔ ∃ pending after, .ok ((term, pending), after) ∈ runs graph marker fuel root ∧
        ∀ obligation ∈ pending, meaning obligation.1 obligation.2) := by
  obtain ⟨bound, allTerms⟩ := finite_uniform_bound graph meaning complete correct marker root
    (Language.enumerate (automaton graph meaning) height root)
    (fun term member => ((bounded_terms_exact graph meaning complete height root term).mp member).1)
  refine ⟨bound, ?_⟩
  intro fuel enough term shallow
  constructor
  · intro accepted
    exact allTerms fuel enough term ((bounded_terms_exact graph meaning complete height root term).mpr ⟨accepted, shallow⟩)
  · rintro ⟨pending, after, success, checked⟩
    exact runs_sound graph meaning complete correct marker fuel root term pending after success checked

end MicroCFTA.EnumerationLanguage
