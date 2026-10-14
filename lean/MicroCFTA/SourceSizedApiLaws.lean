import MicroCFTA.SourceSizedDispatcher
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Exact laws of the complete public Sized query record

The specification retains finite class execution, distinct accepted terms,
signed queries, size-major order, and both term-rank inverses. A reference
row graph derives every field from its actual distinct class recurrence.
-/
namespace MicroCFTA.SourceSizedApiLaws
open Language RecursiveSize SourceSizedDispatcher

/-- All observable exact Sized laws, with finite execution of every source class. -/
structure Exact [DecidableEq Symbol] (api : Api Symbol) (language : Term Symbol → Prop) : Prop where
  finite : ∃ (State : Type) (rows : Automaton State Symbol) (root : State), api = referenceApi rows root ∧
    ∀ size, SourceSizedReference.ClassEvaluation rows (size + 1) size root (api.terms (size : Int))
  distinct : ∀ size, (api.terms size).Nodup
  accepted : ∀ size term, term ∈ api.terms size ↔ language term ∧ (nodeSize term : Int) = size
  counted : ∀ size, api.count size = (api.terms size).length
  rejected : ∀ size rank, api.unrank size rank = none ↔ rank < 0 ∨ (api.count size : Int) ≤ rank
  ranked : ∀ term, (∃ position, api.rank term = some position) ↔ language term
  inverses : ∀ term size rank,
    (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) = some (size, rank) ↔
      api.unrank size rank = some term
  prefixes : ∀ bound, (SourceSizedQueries.through (fun size => api.terms (size : Int)) bound).Nodup ∧
    (SourceSizedQueries.through (fun size => api.terms (size : Int)) bound).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second) ∧
    ∀ term, term ∈ SourceSizedQueries.through (fun size => api.terms (size : Int)) bound ↔ language term ∧ nodeSize term ≤ bound

/-- The actual distinct reference recurrence derives the complete query specification. -/
theorem reference [DecidableEq Symbol] (rows : Automaton State Symbol) (root : State)
    (language : Term Symbol → Prop) (correct : ∀ term, Accepts rows root term ↔ language term) :
    Exact (referenceApi rows root) language := by
  let classes := fun size => SourceSizedReference.classes rows size root
  have natural (size : Nat) : (referenceApi rows root).terms (size : Int) = classes size :=
    SourceSizedQueries.termsSigned_nat classes (SourceSizedReference.classes_zero rows root) size
  have allNatural : (fun size : Nat => (referenceApi rows root).terms (size : Int)) = classes := funext natural
  refine ⟨⟨State, rows, root, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro size
    rw [natural]
    exact SourceSizedReference.classes_evaluation_bound rows size root
  · intro size
    change (SourceSizedQueries.termsSigned classes size).Nodup
    unfold SourceSizedQueries.termsSigned
    split
    · exact List.nodup_nil
    · exact SourceSizedReference.classes_nodup rows _ root
  · intro size term
    exact (SourceSizedReferenceAPI.signed_exact rows root size term).trans (and_congr (correct term) Iff.rfl)
  · intro size
    rfl
  · intro size rank
    exact SourceSizedReferenceAPI.signed_unrank_none_iff rows root size rank
  · intro term
    exact (SourceSizedReferenceAPI.rank_exists_iff rows root term).trans (correct term)
  · intro term size rank
    change SourceSizedQueries.rankSigned classes nodeSize term = some (size, rank) ↔
      SourceSizedQueries.unrankSigned classes size rank = some term
    constructor
    · exact SourceSizedQueries.unrankSigned_rankSigned classes (SourceSizedReference.classes_zero rows root) nodeSize term size rank
    · exact SourceSizedQueries.rankSigned_unrankSigned classes nodeSize (SourceSizedReferenceAPI.classes_sized rows root)
        (fun size => SourceSizedReference.classes_nodup rows size root) term size rank
  · intro bound
    rw [allNatural]
    exact ⟨SourceSizedReferenceAPI.through_nodup rows root bound, SourceSizedReferenceAPI.through_ordered rows root bound,
      fun term => (SourceSizedReferenceAPI.through_exact rows root bound term).trans (and_congr (correct term) Iff.rfl)⟩

end MicroCFTA.SourceSizedApiLaws
