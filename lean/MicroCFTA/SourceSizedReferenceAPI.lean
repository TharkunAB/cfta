import MicroCFTA.SourceSizedReference
import MicroCFTA.SourceSizedQueries

/-!
# The four reference Sized queries and size-major enumeration

All queries use the checked finite class sequence. Both rank inverse laws
hold for distinct terms, including when their accepting runs are ambiguous.
Finite prefixes visit every size through their bound.
-/

namespace MicroCFTA.SourceSizedReferenceAPI

open Language RecursiveSize SourceSizedReference

/-- Every reference member has exactly the requested node count. -/
theorem classes_sized [DecidableEq Symbol] (A : Automaton State Symbol) (state : State) :
    SourceSizedQueries.Sized (fun size => classes A size state) nodeSize := by
  intro size term member
  exact ((mem_classes_iff A size state term).mp member).2

/-- The term rank exists exactly for an accepted finite term. -/
theorem rank_exists_iff [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (term : Term Symbol) :
    (∃ position, SourceSizedQueries.rank (fun size => classes A size state) nodeSize term = some position) ↔
      Accepts A state term := by
  rw [SourceSizedQueries.rank_exists_iff, mem_classes_iff]
  exact and_iff_left rfl

/-- Ranking then selecting recovers the accepted term. -/
theorem unrank_rank [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (term : Term Symbol) (position : SizedRank.Position)
    (found : SourceSizedQueries.rank (fun size => classes A size state) nodeSize term = some position) :
    SourceSizedQueries.unrank (fun size => classes A size state) position = some term :=
  SourceSizedQueries.unrank_rank _ nodeSize term position found

/-- Selecting then ranking recovers both the exact node count and distinct class rank. -/
theorem rank_unrank [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (term : Term Symbol) (position : SizedRank.Position)
    (found : SourceSizedQueries.unrank (fun size => classes A size state) position = some term) :
    SourceSizedQueries.rank (fun size => classes A size state) nodeSize term = some position :=
  SourceSizedQueries.rank_unrank _ nodeSize (classes_sized A state)
    (fun size => classes_nodup A size state) position term found

/-- A finite reference prefix contains exactly accepted terms within the node bound. -/
theorem through_exact [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (bound : Nat) (term : Term Symbol) :
    term ∈ SourceSizedQueries.through (fun size => classes A size state) bound ↔
      Accepts A state term ∧ nodeSize term ≤ bound :=
  SourceSizedQueries.prefix_exact _ nodeSize (Accepts A state)
    (fun size term => mem_classes_iff A size state term) bound term

/-- Every accepted term appears after finitely many size classes, despite empty gaps. -/
theorem through_complete [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (term : Term Symbol) :
    (∃ bound, term ∈ SourceSizedQueries.through (fun size => classes A size state) bound) ↔
      Accepts A state term :=
  SourceSizedQueries.prefix_complete _ nodeSize (Accepts A state)
    (fun size term => mem_classes_iff A size state term) term

/-- Every finite reference prefix is in nondecreasing node-count order. -/
theorem through_ordered [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (bound : Nat) :
    (SourceSizedQueries.through (fun size => classes A size state) bound).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second) :=
  SourceSizedQueries.prefix_ordered _ nodeSize (classes_sized A state) bound

/-- No accepted term is repeated within or across size classes. -/
theorem through_nodup [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (bound : Nat) :
    (SourceSizedQueries.through (fun size => classes A size state) bound).Nodup :=
  SourceSizedQueries.prefix_nodup _ nodeSize (classes_sized A state)
    (fun size => classes_nodup A size state) bound

/-- Signed source size queries preserve the same accepted node-count classes. -/
theorem signed_exact [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (size : Int) (term : Term Symbol) :
    term ∈ SourceSizedQueries.termsSigned (fun size => classes A size state) size ↔
      Accepts A state term ∧ (nodeSize term : Int) = size := by
  by_cases positive : size < 1
  · have impossible : ¬(nodeSize term : Int) = size := by
      have := nodeSize_pos term
      omega
    simp [SourceSizedQueries.termsSigned, positive, impossible]
  · have nonnegative : 0 ≤ size := by omega
    rw [SourceSizedQueries.termsSigned, ite_eq_right positive, mem_classes_iff]
    constructor
    · rintro ⟨accepted, exactSize⟩
      exact ⟨accepted, by omega⟩
    · rintro ⟨accepted, exactSize⟩
      exact ⟨accepted, by omega⟩

/-- The signed selector returns no term exactly outside the valid class ranks. -/
theorem signed_unrank_none_iff [DecidableEq Symbol] (A : Automaton State Symbol)
    (state : State) (size rank : Int) :
    SourceSizedQueries.unrankSigned (fun size => classes A size state) size rank = none ↔
      rank < 0 ∨ (SourceSizedQueries.countSigned (fun size => classes A size state) size : Int) ≤ rank := by
  by_cases negative : rank < 0
  · simp [SourceSizedQueries.unrankSigned, negative]
  · simp only [SourceSizedQueries.unrankSigned, negative, ite_false,
      SourceSizedQueries.countSigned, List.getElem?_eq_none_iff, false_or]
    omega

end MicroCFTA.SourceSizedReferenceAPI
