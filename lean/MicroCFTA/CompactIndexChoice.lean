import MicroCFTA.CompactEdgeRanks

/-!
# Ordered compact alternative indexes

The selector subtracts the counts of earlier alternatives. The inverse uses
the first successful local inverse and adds its offset. The overlap gate
supplies disjointness, so both directions retain the same unique member rank.
-/
namespace MicroCFTA.CompactIndexChoice
open CompactEdgeRanks

/-- Total compact cardinality, in the exact source alternative order. -/
def count (indexes : List (Index Value)) : Nat := (indexes.map Index.count).sum

/-- Source choice selection subtracts each preceding alternative's count. -/
def select : List (Index Value) → Nat → Option Value
  | [], _ => none
  | first :: rest, rank => if rank < first.count then first.select rank else select rest (rank - first.count)

/-- Source rankAlternatives retains the first successful inverse and its offset. -/
def rank : List (Index Value) → Value → Option Nat
  | [], _ => none
  | first :: rest, value => match first.rank value with
      | some found => some found
      | none => (rank rest value).map (first.count + ·)

/-- The exact ordered choice object; source oneof rejects an empty list before constructing it. -/
def choice (indexes : List (Index Value)) : Index Value := ⟨count indexes, select indexes, rank indexes⟩

/-- Distinct source alternatives do not select the same value at any pair of ranks. -/
def Disjoint (indexes : List (Index Value)) : Prop :=
  indexes.Pairwise fun first second => ∀ a b value,
    first.select a = some value → second.select b ≠ some value

/-- Every direct choice selection comes from a concrete alternative. -/
theorem select_origin (indexes : List (Index Value)) (position : Nat) (value : Value)
    (found : select indexes position = some value) :
    ∃ index ∈ indexes, ∃ localRank, index.select localRank = some value := by
  induction indexes generalizing position with
  | nil => cases found
  | cons first rest ih =>
      simp only [select] at found
      split at found
      · exact ⟨first, by simp, position, found⟩
      · obtain ⟨index, member, localRank, selected⟩ := ih _ found
        exact ⟨index, by simp [member], localRank, selected⟩

/-- Choice decoding stays below the sum of all alternative counts. -/
theorem select_bound (indexes : List (Index Value)) (correct : ∀ index ∈ indexes, Correct index)
    (position : Nat) (value : Value) (found : select indexes position = some value) : position < count indexes := by
  induction indexes generalizing position with
  | nil => cases found
  | cons first rest ih =>
      simp only [select] at found
      split at found
      next within => simp only [count, List.map_cons, List.sum_cons]; omega
      next outside =>
        have tail := ih (fun index member => correct index (by simp [member])) _ found
        simp only [count, List.map_cons, List.sum_cons] at *
        omega

/-- Every rank below the total count reaches one complete alternative. -/
theorem select_total (indexes : List (Index Value)) (correct : ∀ index ∈ indexes, Correct index)
    (position : Nat) (within : position < count indexes) : ∃ value, select indexes position = some value := by
  induction indexes generalizing position with
  | nil => simp [count] at within
  | cons first rest ih =>
      by_cases before : position < first.count
      · obtain ⟨value, selected⟩ := (correct first (by simp)).total position before
        exact ⟨value, by simp [select, before, selected]⟩
      · have tailBound : position - first.count < count rest := by
          simp only [count, List.map_cons, List.sum_cons] at within ⊢
          omega
        obtain ⟨value, selected⟩ := ih (fun index member => correct index (by simp [member])) _ tailBound
        exact ⟨value, by simp [select, before, selected]⟩

/-- An earlier disjoint alternative must reject a term selected by a later alternative. -/
theorem earlier_rejects (first : Index Value) (rest : List (Index Value)) (correct : Correct first)
    (disjoint : Disjoint (first :: rest)) (position : Nat) (value : Value)
    (selected : select rest position = some value) : first.rank value = none := by
  obtain ⟨index, member, localRank, chosen⟩ := select_origin rest position value selected
  cases ranked : first.rank value with
  | none => rfl
  | some earlier =>
      have firstChosen := (correct.inverse earlier value).mp ranked
      exact False.elim ((List.pairwise_cons.mp disjoint).1 index member earlier localRank value firstChosen chosen)

/-- Source first-success inverse ranking is exactly the same direct choice position. -/
theorem inverse (indexes : List (Index Value)) (correct : ∀ index ∈ indexes, Correct index)
    (disjoint : Disjoint indexes) (position : Nat) (value : Value) :
    rank indexes value = some position ↔ select indexes position = some value := by
  induction indexes generalizing position with
  | nil => simp [rank, select]
  | cons first rest ih =>
      have localCorrect := correct first (by simp)
      have tailCorrect : ∀ index ∈ rest, Correct index := fun index member => correct index (by simp [member])
      have tailDisjoint := (List.pairwise_cons.mp disjoint).2
      constructor
      · intro ranked
        cases firstRank : first.rank value with
        | some found =>
            have same : found = position := by simpa [rank, firstRank] using ranked
            subst found
            have selected := (localCorrect.inverse position value).mp firstRank
            have bounded := localCorrect.bounded position value selected
            simp [select, bounded, selected]
        | none =>
            obtain ⟨localRank, localFound, same⟩ := Option.map_eq_some_iff.mp (by simpa [rank, firstRank] using ranked)
            have selected := (ih tailCorrect tailDisjoint localRank).mp localFound
            subst position
            simp [select, show ¬first.count + localRank < first.count by omega, selected]
      · intro selected
        by_cases before : position < first.count
        · have selectedFirst : first.select position = some value := by simpa [select, before] using selected
          simp [rank, (localCorrect.inverse position value).mpr selectedFirst]
        · have selectedTail : select rest (position - first.count) = some value := by simpa [select, before] using selected
          have firstNone := earlier_rejects first rest localCorrect disjoint _ value selectedTail
          have tailRanked := (ih tailCorrect tailDisjoint _).mpr selectedTail
          simp [rank, firstNone, tailRanked, show first.count + (position - first.count) = position by omega]

/-- Ordered compact union derives the complete operational index invariant. -/
theorem choice_correct (indexes : List (Index Value)) (correct : ∀ index ∈ indexes, Correct index)
    (disjoint : Disjoint indexes) : Correct (choice indexes) where
  bounded := select_bound indexes correct
  total := select_total indexes correct
  inverse position value := inverse indexes correct disjoint position value

/-- A member from one alternative occurs at its prefix-offset choice rank. -/
theorem select_member (before after : List (Index Value)) (index : Index Value)
    (correct : ∀ source ∈ before ++ index :: after, Correct source) (position : Nat) (value : Value)
    (selected : index.select position = some value) :
    select (before ++ index :: after) (count before + position) = some value := by
  induction before with
  | nil =>
      have bound := (correct index (by simp)).bounded position value selected
      simp [select, count, bound, selected]
  | cons first rest ih =>
      have tailCorrect : ∀ source ∈ rest ++ index :: after, Correct source := fun source member => correct source (by simp [member])
      have tail := ih tailCorrect
      simp only [count, List.map_cons, List.sum_cons, List.cons_append, select]
      rw [ite_eq_right (by omega)]
      simpa only [count, Nat.add_assoc, Nat.add_sub_cancel_left] using tail

/-- Compact union inserts and removes no member of any alternative. -/
theorem language_exact (indexes : List (Index Value)) (correct : ∀ index ∈ indexes, Correct index)
    (value : Value) :
    (∃ position, select indexes position = some value) ↔
      ∃ index ∈ indexes, ∃ position, index.select position = some value := by
  constructor
  · rintro ⟨position, selected⟩; exact select_origin indexes position value selected
  · rintro ⟨index, member, position, selected⟩
    obtain ⟨before, after, same⟩ := List.append_of_mem member
    subst indexes
    exact ⟨count before + position, select_member before after index correct position value selected⟩

end MicroCFTA.CompactIndexChoice
