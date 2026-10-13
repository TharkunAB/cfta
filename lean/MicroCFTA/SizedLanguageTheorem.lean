import MicroCFTA.SourceSizedPublicContracts
import MicroCFTA.Construction

/-!
# The exact language-generation theorem by node-count size

The grammar judgment describes the language independently of the generated
lists. The compiled reference worker terminates at each requested size, even
when the complete language is infinite. Empty size classes do not terminate
the sequence. Every term has one size and one rank within that size.

The public theorem uses the actual Sized preprocessing and dispatch. It
retains the source constraint-cache invariant. The separate liquid theorem
handles external decisions; this theorem does not assume solver termination.
-/

namespace MicroCFTA.SizedLanguageTheorem

open Language RecursiveSize Construction

/-- The main mathematical contract needs neither a finite language nor unambiguous runs. -/
theorem grammar_correct [DecidableEq Symbol]
    (grammar : Grammar Nonterminal Symbol) (start : Pattern Nonterminal Symbol) :
    let A := compile grammar
    let terms := fun size => SourceSizedReference.classes A size start
    (∀ size term, term ∈ terms size ↔ Derives grammar start term ∧ nodeSize term = size) ∧
    (∀ size, SourceSizedReference.ClassEvaluation A (size + 1) size start (terms size)) ∧
    (∀ bound, (SourceSizedQueries.through terms bound).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ bound, (SourceSizedQueries.through terms bound).Nodup) ∧
    (∀ term, (∃ bound, term ∈ SourceSizedQueries.through terms bound) ↔ Derives grammar start term) ∧
    (∀ term position, SourceSizedQueries.rank terms nodeSize term = some position ↔
      SourceSizedQueries.unrank terms position = some term) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro size term
    rw [SourceSizedReference.mem_classes_iff, compile_exact]
  · exact fun size => SourceSizedReference.classes_evaluation_bound _ size start
  · exact SourceSizedReferenceAPI.through_ordered (compile grammar) start
  · exact SourceSizedReferenceAPI.through_nodup (compile grammar) start
  · intro term
    rw [SourceSizedReferenceAPI.through_complete, compile_exact]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank (compile grammar) start term position,
      SourceSizedReferenceAPI.rank_unrank (compile grammar) start term position⟩

open SourceSizedDecided SourceSizedDispatcher SourceSizedPreprocessing
open SourceGuards SourceObservations SourceSymbolicIndex

/-- The public Sized result has exact finite classes, size order, complete coverage, and both inverses. -/
theorem public_correct [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State (Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (active : ∀ state row,
      row ∈ SourceSizedTrimGuards.trimmedRows input.rows input.states input.root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (api : Api (Label Formula)) (success : publicSized input = .ok api) :
    (∀ (size : Nat) term, term ∈ api.terms (size : Int) ↔
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term ∧
        nodeSize term = size) ∧
    (∀ size, SourceSizedReference.ClassEvaluation (equalityRows (sortedRows input))
      (size + 1) size input.root (api.terms (size : Int))) ∧
    (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second)) ∧
    (∀ bound, (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Nodup) ∧
    (∀ term, (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound) ↔
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term) ∧
    (∀ size rank term,
      (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) =
        some (size, rank) ↔ api.unrank size rank = some term) := by
  exact ⟨publicSized_terms_exact formulas solver input active api success,
    SourceSizedPublicContracts.finite_class input api success,
    SourceSizedPublicContracts.size_ordered input api success,
    SourceSizedPublicContracts.enumeration_nodup input api success,
    SourceSizedPublicContracts.enumeration_complete input api success formulas solver active,
    publicSized_signed_inverses input api success⟩

end MicroCFTA.SizedLanguageTheorem
