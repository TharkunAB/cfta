import MicroCFTA.SourceCyclicRowsProbability

/-!
# Shared row readback through cyclic sampling and public PMFs

Completed source traversal and successful current compilation construct the
probability record. The theorem below refers to the original guarded heap
language. It derives each sampler and PMF contract from the source counts
and inverse callbacks, without an assumed normalized class sampler.
-/

namespace MicroCFTA.SourceCyclicRowsProbabilityReadback

open Language Probability RecursiveSize SizedRank SourceGuards SourceObservations SourceSymbolicIndex
open SourceInternedRows SourceDenseRows SourceCyclicRowsProbability

/-- Actual shared-row cyclic imports have exact PMF keys, masses, support, and sampled inverse ranks. -/
theorem source_correct [DecidableEq Formula] [DecidableEq Key] [Ord Key] [Ord (Term (Label Formula))]
    (heap : Heap (Label Formula) (Constraint Formula)) (fuel : Nat) (rootRef : Ref)
    (raw : SourceCyclicRowsReadback.Table Formula) (read : toRows heap fuel rootRef = some raw)
    (noEmpty : NoEmptyBelow heap rootRef) (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (output : Automaton (Member (SourceDenseRows.keys raw)) (Label Formula))
    (success : SourceCyclicRows.compile formulas solver
      (SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active) order = some (.ok output))
    (fallback : Term (Label Formula)) :
    let input := SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active
    let actual := record output input.root fallback
    (∀ size term, term ∈ (SourcePmfQuery.recursiveAtSize actual size).map Prod.fst ↔
      Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧ (nodeSize term : Int) = size) ∧
    (∀ size term, eventMass (fun found => found == term)
      ((SourcePmfQuery.recursiveAtSize actual size).map Prod.swap) =
        @ite Rat (Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧
          (nodeSize term : Int) = size) (Classical.propDecidable _)
          (1 / (countAt output size.toNat input.root : Rat)) 0) ∧
    (∀ size term, (∃ rank mass, 0 < mass ∧ (mass, (rank, term)) ∈ (actual.sampling size).ranked) ↔
      Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧ (nodeSize term : Int) = size) ∧
    (∀ size, 0 < countAt output size.toNat input.root →
      IsProbability (actual.sampling size).values ∧ IsProbability (actual.sampling size).ranked ∧
        IsProbability ((SourcePmfQuery.recursiveAtSize actual size).map Prod.swap)) ∧
    (∀ size : Nat, ∀ entry ∈ (actual.sampling size).ranked,
      replayPosition output input.root ⟨size, entry.2.1⟩ = some entry.2.2 ∧
      TablePosition.positionsOf output entry.2.2 input.root = some ⟨size, entry.2.1⟩) := by
  dsimp only
  let input := SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active
  have language := SourceCyclicRowsReadback.root_language heap fuel rootRef raw read noEmpty
    formulas solver freeVariables active
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro size term
    exact (pmf_keys formulas solver input order output success fallback term size).trans
      (and_congr (language term) Iff.rfl)
  · intro size term
    have mass := term_mass formulas solver input order output success fallback term size
    classical
    by_cases accepted : Accepts (SourceCyclicRows.original formulas solver input) input.root term
    · have actual := (language term).mp accepted
      simpa only [accepted, actual, true_and] using mass
    · have actual : ¬Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term :=
        fun found => accepted ((language term).mpr found)
      simpa only [accepted, actual, false_and, ↓reduceIte] using mass
  · intro size term
    exact (sampled_support formulas solver input order output success fallback term size).trans
      (and_congr (language term) Iff.rfl)
  · exact probability output input.root fallback
  · exact sampled_inverse formulas solver input order output success fallback

end MicroCFTA.SourceCyclicRowsProbabilityReadback
