import MicroCFTA.SourceSizedDecidedOrder
import MicroCFTA.SourceSizedQueries

/-!
# The query laws of a successful decided size table

All four queries use the same distinct class sequence. Signed queries keep
the source invalid-size and invalid-rank behavior. Every finite enumeration
prefix is distinct and ordered by node count, including across empty classes.
-/

namespace MicroCFTA.SourceSizedDecidedQueries

open Language RecursiveSize SourceSizedDecided SourceSizedDecidedTable

section Table

variable [DecidableEq State] [DecidableEq Symbol]
  (rows : State → List (Row State Symbol Constraint)) (states : List State)
  (answer : Constraint × Term Symbol → Guards.Verdict)
  (holds : Constraint → Term Symbol → Bool)
  (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
  (bound : Nat) (output : Table State (Term Symbol))
  (success : sizedUpTo rows states answer bound = .ok output) (root : State)

include adequate success

/-- A successful table has no size-zero terms. -/
theorem zero_class : output root 0 = [] := by
  rw [sizedUpTo_exact rows states answer holds adequate bound output success root 0]
  simp

/-- The class index is the exact node count of each member. -/
theorem class_sized : SourceSizedQueries.Sized (output root) nodeSize := by
  intro size term present
  exact ((sizedUpTo_member_iff rows states answer holds adequate bound output success root size term).mp present).2.2.2.2

omit [DecidableEq State] adequate success in
/-- Selecting a ranked term returns that exact term. -/
theorem unrank_rank (term : Term Symbol) (position : SizedRank.Position)
    (found : SourceSizedQueries.rank (output root) nodeSize term = some position) :
    SourceSizedQueries.unrank (output root) position = some term :=
  SourceSizedQueries.unrank_rank (output root) nodeSize term position found

/-- Ranking a selected term returns its exact size and class rank. -/
theorem rank_unrank (term : Term Symbol) (position : SizedRank.Position)
    (found : SourceSizedQueries.unrank (output root) position = some term) :
    SourceSizedQueries.rank (output root) nodeSize term = some position :=
  SourceSizedQueries.rank_unrank (output root) nodeSize
    (class_sized rows states answer holds adequate bound output success root)
    (sizedUpTo_nodup rows states answer holds adequate bound output success root) position term found

/-- The source signed rank followed by signed selection returns the term. -/
theorem unrankSigned_rankSigned (term : Term Symbol) (size index : Int)
    (found : SourceSizedQueries.rankSigned (output root) nodeSize term = some (size, index)) :
    SourceSizedQueries.unrankSigned (output root) size index = some term :=
  SourceSizedQueries.unrankSigned_rankSigned (output root)
    (zero_class rows states answer holds adequate bound output success root) nodeSize term size index found

/-- Source signed selection followed by ranking preserves both source integers. -/
theorem rankSigned_unrankSigned (term : Term Symbol) (size index : Int)
    (found : SourceSizedQueries.unrankSigned (output root) size index = some term) :
    SourceSizedQueries.rankSigned (output root) nodeSize term = some (size, index) :=
  SourceSizedQueries.rankSigned_unrankSigned (output root) nodeSize
    (class_sized rows states answer holds adequate bound output success root)
    (sizedUpTo_nodup rows states answer holds adequate bound output success root) term size index found

/-- Enumeration through any size is ordered by nondecreasing node count. -/
theorem size_ordered (throughSize : Nat) :
    (SourceSizedQueries.through (output root) throughSize).Pairwise
      (fun first second => nodeSize first ≤ nodeSize second) :=
  SourceSizedQueries.prefix_ordered (output root) nodeSize
    (class_sized rows states answer holds adequate bound output success root) throughSize

/-- Enumeration contains no duplicate term within or across sizes. -/
theorem enumeration_nodup (throughSize : Nat) :
    (SourceSizedQueries.through (output root) throughSize).Nodup :=
  SourceSizedQueries.prefix_nodup (output root) nodeSize
    (class_sized rows states answer holds adequate bound output success root)
    (sizedUpTo_nodup rows states answer holds adequate bound output success root) throughSize

end Table

section Original

open SourceSizedDecidedTrim SourceSizedDecidedOrder

variable [DecidableEq State] [DecidableEq Symbol]
  (nodes : List State) (complete : ∀ state, state ∈ nodes)
  (original : Automaton State Symbol)
  (rows : State → List (Row State Symbol Constraint))
  (answer : Constraint × Term Symbol → Guards.Verdict)
  (holds : Constraint → Term Symbol → Bool)
  (rowOrder : ∀ state, (automaton rows holds state).Perm (original state))
  (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
  (root : State) (bound : Nat) (output : Table State (Term Symbol))
  (success : sizedUpTo rows (trimKeys nodes original root) answer bound = .ok output)

include complete rowOrder adequate success

/-- The decided count equals the reference count through the bound and zero above it. -/
theorem count_reference (size : Nat) :
    SourceSizedQueries.count (output root) size =
      if size ≤ bound then (SourceSizedReference.classes (automaton rows holds) size root).length else 0 := by
  unfold SourceSizedQueries.count
  rw [sizedUpTo_reference_order nodes complete original rows answer holds rowOrder adequate root bound output success size]
  split <;> rfl

/-- Ranking succeeds exactly for accepted original terms within the bound. -/
theorem rank_exists_iff (term : Term Symbol) :
    (∃ position, SourceSizedQueries.rank (output root) nodeSize term = some position) ↔
      Accepts original root term ∧ nodeSize term ≤ bound := by
  rw [SourceSizedQueries.rank_exists_iff,
    sizedUpTo_original_iff nodes complete original rows answer holds rowOrder adequate root bound output success]
  simp

/-- A finite enumeration prefix has exactly the accepted terms within both bounds. -/
theorem enumeration_exact (throughSize : Nat) (term : Term Symbol) :
    term ∈ SourceSizedQueries.through (output root) throughSize ↔
      Accepts original root term ∧ nodeSize term ≤ bound ∧ nodeSize term ≤ throughSize := by
  rw [SourceSizedQueries.mem_prefix]
  constructor
  · rintro ⟨size, below, present⟩
    obtain ⟨accepted, exactSize, bounded⟩ := (sizedUpTo_original_iff nodes complete original rows answer
      holds rowOrder adequate root bound output success size term).mp present
    exact ⟨accepted, by omega, by omega⟩
  · rintro ⟨accepted, bounded, below⟩
    refine ⟨nodeSize term, below, ?_⟩
    exact (sizedUpTo_original_iff nodes complete original rows answer holds rowOrder adequate root bound output
      success (nodeSize term) term).mpr ⟨accepted, rfl, bounded⟩

end Original

end MicroCFTA.SourceSizedDecidedQueries
