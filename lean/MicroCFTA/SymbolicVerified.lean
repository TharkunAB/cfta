import MicroCFTA.SymbolicCounter
import MicroCFTA.SymbolicIndicators

/-!
# Source ranks from concrete graph and guard semantics

These theorems use the actual bounded count, selection, and inverse drivers.
They derive counter correctness from graph rows and compiled guards. The
completeness theorem retains only the sufficient-bound totality obligation.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- A successful actual decode is accepted and has its exact inverse, with the counter fully proved. -/
theorem rows_decode_correct [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph) (fallback : Term Symbol)
    (intersection : ∀ left right term,
      term ∈ meaning.terms (graph.intersect left right) ↔ term ∈ meaning.terms left ∧ term ∈ meaning.terms right)
    (guard : Edge Symbol → Term Symbol → Bool)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (rows : ∀ node term, term ∈ meaning.terms node ↔
      ∃ edge ∈ graph.edges node, ShapeHolds meaning.terms edge term ∧ guard edge term = true)
    (fuel root : Nat) (rank : Int) (term : Term Symbol)
    (success : unrank graph order fuel root rank = .ok term) :
    term ∈ meaning.terms root ∧ rankOf graph order fuel root term = .ok (some rank) := by
  let counter := counterMeaningFromRows graph meaning.terms meaning.distinct intersection guard compiled rows
  exact unrank_sound_and_inverse graph order meaning (SemanticCache meaning.terms) (semanticCache_empty meaning.terms)
    (counter_countSound graph counter fallback) fuel root rank term success

/-- Concrete row semantics and sufficient execution bounds give exactly the full finite source rank bijection. -/
theorem rows_rank_bijection [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph) (fallback : Term Symbol)
    (intersection : ∀ left right term,
      term ∈ meaning.terms (graph.intersect left right) ↔ term ∈ meaning.terms left ∧ term ∈ meaning.terms right)
    (guard : Edge Symbol → Term Symbol → Bool)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (rows : ∀ node term, term ∈ meaning.terms node ↔
      ∃ edge ∈ graph.edges node, ShapeHolds meaning.terms edge term ∧ guard edge term = true)
    (fuel root : Nat) (total : DecodeTotal graph order fuel root (meaning.terms root).length)
    (term : Term Symbol) (accepted : term ∈ meaning.terms root) :
    ∃ rank : Fin (meaning.terms root).length,
      unrank graph order fuel root rank.val = .ok term ∧
      rankOf graph order fuel root term = .ok (some rank.val) ∧
      ∀ other : Fin (meaning.terms root).length,
        unrank graph order fuel root other.val = .ok term → other = rank := by
  let counter := counterMeaningFromRows graph meaning.terms meaning.distinct intersection guard compiled rows
  exact source_rank_bijection graph order meaning (SemanticCache meaning.terms) (semanticCache_empty meaning.terms)
    (counter_countSound graph counter fallback) fuel root total term accepted

end MicroCFTA.SymbolicDriver
