import MicroCFTA.SourceSizedPublicContracts
import MicroCFTA.System

/-!
# Distinct-term sampling through the public Sized queries

Sized exposes queries, not a sampling operation. This module proves the
composition of those queries with uniform class-rank sampling and the
existing exact weighted-ticket sampler. A backend must draw a uniform rank
below the positive count. Requested term weights are separate from accepting
run multiplicity and from weights of generic generator members.
-/

namespace MicroCFTA.SourceSizedSampling

open Language RecursiveSize Probability SourceSizedDecided SourceSizedDispatcher
open SourceSizedPreprocessing SourceGuards SourceObservations SourceSymbolicIndex

/-- The exact distribution obtained by drawing a class rank and calling public unrank. -/
def uniformQuery (api : Api Symbol) (size : Int) : Distribution (Option (Term Symbol)) :=
  Probability.map (fun rank : Nat => api.unrank size rank)
    (normalize (counting (List.range (api.count size))))

variable [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
  (input : Input State (Label Formula) (Constraint Formula))
  (api : Api (Label Formula)) (success : publicSized input = .ok api)

include success

/-- Uniform valid class ranks sample the exact public term list, each once. -/
theorem uniformQuery_exact (size : Int) :
    uniformQuery api size = Probability.map some (normalize (counting (api.terms size))) := by
  obtain ⟨_, rfl⟩ := publicSized_success input api success
  unfold uniformQuery
  rw [Sampler.map_normalize, Sampler.map_counting, Sampler.map_normalize, Sampler.map_counting]
  change normalize (counting ((List.range _).map _)) = normalize (counting (List.map some _))
  congr 2
  dsimp only [referenceApi, SourceSizedQueries.countSigned]
  have lookups : (fun rank : Nat => SourceSizedQueries.unrankSigned
      (fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root) size rank) =
      (fun rank : Nat => (SourceSizedQueries.termsSigned
        (fun size => SourceSizedReference.classes (equalityRows (sortedRows input)) size input.root) size)[rank]?) := by
    funext rank
    have nonnegative := Int.natCast_nonneg rank
    simp [SourceSizedQueries.unrankSigned, show ¬(rank : Int) < 0 by omega]
  rw [lookups]
  exact Sampler.map_range_get _

/-- A decoded rank never contributes probability to an absent result. -/
theorem uniformQuery_no_failure (size : Int) :
    eventMass (fun term => term.isNone) (uniformQuery api size) = 0 := by
  rw [uniformQuery_exact input api success, eventMass_map]
  exact eventMass_false _

/-- Positive public cardinality makes the decoded class distribution a probability law. -/
theorem uniformQuery_probability (size : Int) (nonempty : 0 < api.count size) :
    IsProbability (uniformQuery api size) := by
  rw [uniformQuery_exact input api success, Sampler.map_normalize, Sampler.map_counting]
  apply uniform_probability
  rw [List.length_map]
  rw [SourceSizedPublicContracts.count_exact input api success] at nonempty
  exact nonempty

variable (formulas : Formulas Formula) (solver : Entailment Formula)
  (active : ∀ state row,
    row ∈ SourceSizedTrimGuards.trimmedRows input.rows input.states input.root state →
    SourceCompactGuards.ActiveOption row.constraint.equalities)

include active

/-- The actual public class is an index of precisely the described terms at this size. -/
def classIndex (size : Nat) :
    DistinctRank.Index (fun term =>
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term ∧
        nodeSize term = size) where
  members := api.terms size
  nodup := SourceSizedPublicContracts.class_nodup input api success size
  exact := publicSized_terms_exact formulas solver input active api success size

/-- Every accepted term gets equal probability when its distinct class ranks are uniform. -/
theorem uniform_term_probability (size : Nat) (term : Term (Label Formula))
    (accepted : Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term)
    (sized : nodeSize term = size) :
    eventMass (fun found => found == some term) (uniformQuery api size) =
      1 / (api.count size : Rat) := by
  rw [uniformQuery_exact input api success, eventMass_map]
  have probability := DistinctRank.Index.uniform_term_probability
    (classIndex input api success formulas solver active size) term ⟨accepted, sized⟩
  simpa [classIndex, DistinctRank.Index.count, Function.comp_def,
    SourceSizedPublicContracts.count_exact input api success] using probability

/-- Requested nonnegative weights normalize on the distinct class, independently of its runs. -/
theorem requested_probability (size : Nat) (weight : Term (Label Formula) → Rat)
    (nonnegative : ∀ term,
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term →
      nodeSize term = size → 0 ≤ weight term)
    (positive : 0 < total (System.weightedMembers
      (classIndex input api success formulas solver active size) weight)) :
    IsProbability (System.requested
      (classIndex input api success formulas solver active size) weight) :=
  System.requested_probability _ weight (fun term valid => nonnegative term valid.1 valid.2) positive

/-- The probability of each accepted term is exactly its weight divided by total class weight. -/
theorem requested_term_probability (size : Nat) (weight : Term (Label Formula) → Rat)
    (term : Term (Label Formula))
    (accepted : Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term)
    (sized : nodeSize term = size) :
    let index := classIndex input api success formulas solver active size
    eventMass (fun found => decide (found = term)) (System.requested index weight) =
      weight term / total (System.weightedMembers index weight) :=
  System.requested_term_probability _ weight term ⟨accepted, sized⟩

/-- The existing compiled rational-ticket sampler realizes the requested term probabilities. -/
theorem compiled_weighted_event (size : Nat) (weight : Term (Label Formula) → Rat)
    (nonempty : api.terms (size : Int) ≠ [])
    (positive : ∀ term,
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term →
      nodeSize term = size → 0 < weight term)
    (event : Term (Label Formula) → Bool) :
    let index := classIndex input api success formulas solver active size
    let masses := System.weightedMembers index weight
    eventMass (fun result => result.any event)
        (Sampler.binarySampling (Sampler.groupWeighted (Sampler.integerMasses masses))) =
      eventMass event (System.requested index weight) := by
  apply Sampler.compiled_rational_probability
  · simpa [System.weightedMembers, classIndex] using nonempty
  · intro entry member
    obtain ⟨term, present, rfl⟩ := List.mem_map.mp member
    have valid := (publicSized_terms_exact formulas solver input active api success size term).mp present
    exact positive term valid.1 valid.2

end MicroCFTA.SourceSizedSampling
