import MicroCFTA.SourceSizedPreprocessing
import MicroCFTA.SourceSizedReferenceAPI

/-!
# The public Sized language, completion, and size-order contracts

These statements include the actual canonical preprocessing and both query
branches. Each successful result uses the same finite reference class.
An enumeration prefix visits every size through its bound.
-/

namespace MicroCFTA.SourceSizedPublicContracts

open Language RecursiveSize SourceSizedDecided SourceSizedDispatcher SourceSizedPreprocessing
open SourceGuards SourceObservations SourceSymbolicIndex

variable [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
  (input : Input State (Label Formula) (Constraint Formula))
  (api : Api (Label Formula)) (success : publicSized input = .ok api)

include success

/-- The public count is precisely the length of the public ordered class. -/
theorem count_exact (size : Int) : api.count size = (api.terms size).length := by
  obtain ⟨_, rfl⟩ := publicSized_success input api success
  rfl

/-- The public class has a finite evaluation with strictly decreasing size queries. -/
theorem finite_class (size : Nat) :
    SourceSizedReference.ClassEvaluation (equalityRows (sortedRows input)) (size + 1) size
      input.root (api.terms (size : Int)) := by
  obtain ⟨_, rfl⟩ := publicSized_success input api success
  dsimp only [referenceApi]
  rw [SourceSizedQueries.termsSigned_nat
    (fun n => SourceSizedReference.classes (equalityRows (sortedRows input)) n input.root)
    (SourceSizedReference.classes_zero _ _) size]
  exact SourceSizedReference.classes_evaluation_bound _ size input.root

/-- Public natural-size classes have no duplicates. -/
theorem class_nodup (size : Nat) : (api.terms (size : Int)).Nodup := by
  obtain ⟨_, rfl⟩ := publicSized_success input api success
  dsimp only [referenceApi]
  rw [SourceSizedQueries.termsSigned_nat
    (fun n => SourceSizedReference.classes (equalityRows (sortedRows input)) n input.root)
    (SourceSizedReference.classes_zero _ _) size]
  exact SourceSizedReference.classes_nodup _ size input.root

/-- Every member's node count equals its public class size. -/
theorem class_sized : SourceSizedQueries.Sized (fun size : Nat => api.terms size) nodeSize := by
  obtain ⟨_, rfl⟩ := publicSized_success input api success
  intro size term member
  dsimp only [referenceApi] at member
  rw [SourceSizedQueries.termsSigned_nat
    (fun n => SourceSizedReference.classes (equalityRows (sortedRows input)) n input.root)
    (SourceSizedReference.classes_zero _ _) size] at member
  exact ((SourceSizedReference.mem_classes_iff _ size input.root term).mp member).2

/-- Public size-major enumeration is ordered by the actual node count. -/
theorem size_ordered (bound : Nat) :
    (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second) :=
  SourceSizedQueries.prefix_ordered _ nodeSize (class_sized input api success) bound

/-- Public size-major enumeration contains each term only once. -/
theorem enumeration_nodup (bound : Nat) :
    (SourceSizedQueries.through (fun size : Nat => api.terms size) bound).Nodup :=
  SourceSizedQueries.prefix_nodup _ nodeSize (class_sized input api success)
    (class_nodup input api success) bound

/-- A finite public prefix contains exactly the original accepted terms within its bound. -/
theorem enumeration_exact
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (active : ∀ state row,
      row ∈ SourceSizedTrimGuards.trimmedRows input.rows input.states input.root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (bound : Nat) (term : Term (Label Formula)) :
    term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound ↔
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term ∧
        nodeSize term ≤ bound :=
  SourceSizedQueries.prefix_exact _ nodeSize _
    (fun size term => publicSized_terms_exact formulas solver input active api success size term) bound term

/-- Every original accepted finite term appears after finitely many public size classes. -/
theorem enumeration_complete
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (active : ∀ state row,
      row ∈ SourceSizedTrimGuards.trimmedRows input.rows input.states input.root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (term : Term (Label Formula)) :
    (∃ bound, term ∈ SourceSizedQueries.through (fun size : Nat => api.terms size) bound) ↔
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term :=
  SourceSizedQueries.prefix_complete _ nodeSize _
    (fun size term => publicSized_terms_exact formulas solver input active api success size term) term

end MicroCFTA.SourceSizedPublicContracts
