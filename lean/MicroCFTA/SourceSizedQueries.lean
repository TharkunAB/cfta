import MicroCFTA.SizedRank
import MicroCFTA.DistinctRank

/-!
# Queries of a distinct exact-size sequence

This module models `Data.CFTA.Sized.fromClasses`. The caller supplies the
classes. Their construction and guard decisions have separate proofs.
The signed wrappers retain negative-size and negative-rank rejection.
Finite prefixes include every size through the bound, including empty sizes.
-/

namespace MicroCFTA.SourceSizedQueries

open SizedRank

variable {α : Type}

/-- Count the members of one class. -/
def count (classes : Nat → List α) (size : Nat) : Nat := (classes size).length

/-- Select a class member by its zero-based position. -/
def unrank (classes : Nat → List α) (position : Position) : Option α :=
  (classes position.size)[position.rank]?

/-- Search the class at the member's own size. -/
def rank [DecidableEq α] (classes : Nat → List α) (sizeOf : α → Nat)
    (value : α) : Option Position :=
  (rankOf (classes (sizeOf value)) value).map (Position.mk (sizeOf value))

/-- Each member has the size of its class. -/
def Sized (classes : Nat → List α) (sizeOf : α → Nat) : Prop :=
  ∀ size value, value ∈ classes size → sizeOf value = size

/-- A successful inverse query selects the original member. -/
theorem unrank_rank [DecidableEq α] (classes : Nat → List α) (sizeOf : α → Nat)
    (value : α) (position : Position) (found : rank classes sizeOf value = some position) :
    unrank classes position = some value := by
  unfold rank at found
  obtain ⟨index, lookup, same⟩ := Option.map_eq_some_iff.mp found
  subst position
  exact rankOf_replay _ _ index lookup

/-- Ranking a selected member returns its exact size and class rank. -/
theorem rank_unrank [DecidableEq α] (classes : Nat → List α) (sizeOf : α → Nat)
    (sized : Sized classes sizeOf) (distinct : ∀ size, (classes size).Nodup)
    (position : Position) (value : α) (found : unrank classes position = some value) :
    rank classes sizeOf value = some position := by
  have member := List.mem_of_getElem? found
  have sameSize := sized position.size value member
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp found
  have inverse := rankOf_get (classes position.size) (distinct _) position.rank valid
  rw [same] at inverse
  simp [rank, sameSize, inverse]

/-- A rank exists exactly when the member is in its own class. -/
theorem rank_exists_iff [DecidableEq α] (classes : Nat → List α) (sizeOf : α → Nat)
    (value : α) :
    (∃ position, rank classes sizeOf value = some position) ↔ value ∈ classes (sizeOf value) := by
  simp only [rank, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, index, found, _⟩
    exact (rankOf_exists_iff _ _).mp ⟨index, found⟩
  · intro member
    obtain ⟨index, found⟩ := (rankOf_exists_iff _ _).mpr member
    exact ⟨⟨sizeOf value, index⟩, index, found, rfl⟩

/-- Selection succeeds exactly below the class count. -/
theorem unrank_exists_iff (classes : Nat → List α) (position : Position) :
    (∃ value, unrank classes position = some value) ↔ position.rank < count classes position.size := by
  constructor
  · rintro ⟨value, found⟩
    exact (List.getElem?_eq_some_iff.mp found).1
  · intro valid
    exact ⟨(classes position.size)[position.rank], List.getElem?_eq_getElem valid⟩

/-- A class with an exact membership law is a distinct-term index. -/
def index (classes : Nat → List α) (valid : Nat → α → Prop)
    (distinct : ∀ size, (classes size).Nodup)
    (exact : ∀ size value, value ∈ classes size ↔ valid size value) (size : Nat) :
    DistinctRank.Index (valid size) :=
  ⟨classes size, distinct size, exact size⟩

/-- Source sizes below one contain no term. -/
def termsSigned (classes : Nat → List α) (size : Int) : List α :=
  if size < 1 then [] else classes size.toNat

/-- The signed count uses the same ordered class. -/
def countSigned (classes : Nat → List α) (size : Int) : Nat :=
  (termsSigned classes size).length

/-- The signed selector rejects negative ranks before reading the list. -/
def unrankSigned (classes : Nat → List α) (size index : Int) : Option α :=
  if index < 0 then none else (termsSigned classes size)[index.toNat]?

/-- The source drop-and-head selector equals list indexing. -/
theorem drop_head_eq_unrankSigned (classes : Nat → List α) (size index : Int) :
    (if index < 0 then none else ((termsSigned classes size).drop index.toNat).head?) =
      unrankSigned classes size index := by
  simp [unrankSigned]

/-- Every nonpositive source size has an empty class. -/
theorem termsSigned_nonpositive (classes : Nat → List α) (size : Int) (invalid : size ≤ 0) :
    termsSigned classes size = [] := by simp [termsSigned, show size < 1 by omega]

/-- Every negative class rank is rejected. -/
theorem unrankSigned_negative (classes : Nat → List α) (size index : Int) (invalid : index < 0) :
    unrankSigned classes size index = none := by simp [unrankSigned, invalid]

/-- Natural size queries retain the original class when size zero is empty. -/
theorem termsSigned_nat (classes : Nat → List α) (zero : classes 0 = []) (size : Nat) :
    termsSigned classes (size : Int) = classes size := by
  cases size with
  | zero => simp [termsSigned, zero]
  | succ size =>
      have positive : ¬((size + 1 : Nat) : Int) < 1 := by omega
      unfold termsSigned
      rw [ite_eq_right positive]
      rfl

/-- Valid natural positions use the same selector through the signed API. -/
theorem unrankSigned_nat (classes : Nat → List α) (zero : classes 0 = []) (position : Position) :
    unrankSigned classes (position.size : Int) (position.rank : Int) =
      unrank classes position := by
  have nonneg := Int.natCast_nonneg position.rank
  simp only [unrankSigned, show ¬((position.rank : Int) < 0) from Int.not_lt.mpr nonneg,
    ite_false, termsSigned_nat classes zero, Int.toNat_natCast, unrank]

/-- The source inverse returns the member's size and first class index as integers. -/
def rankSigned [DecidableEq α] (classes : Nat → List α) (sizeOf : α → Nat)
    (value : α) : Option (Int × Int) :=
  (rank classes sizeOf value).map fun position => (position.size, position.rank)

/-- Signed rank followed by signed selection returns the original member. -/
theorem unrankSigned_rankSigned [DecidableEq α] (classes : Nat → List α)
    (zero : classes 0 = []) (sizeOf : α → Nat) (value : α) (size index : Int)
    (found : rankSigned classes sizeOf value = some (size, index)) :
    unrankSigned classes size index = some value := by
  unfold rankSigned at found
  obtain ⟨position, ranked, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  rw [unrankSigned_nat classes zero]
  exact unrank_rank classes sizeOf value position ranked

/-- Signed selection followed by ranking preserves both source integers. -/
theorem rankSigned_unrankSigned [DecidableEq α] (classes : Nat → List α)
    (sizeOf : α → Nat) (sized : Sized classes sizeOf)
    (distinct : ∀ size, (classes size).Nodup) (value : α) (size index : Int)
    (found : unrankSigned classes size index = some value) :
    rankSigned classes sizeOf value = some (size, index) := by
  unfold unrankSigned at found
  split at found
  next invalid => cases found
  next nonnegative =>
    unfold termsSigned at found
    split at found
    next invalid => simp at found
    next positive =>
      have decoded : unrank classes ⟨size.toNat, index.toNat⟩ = some value := found
      have ranked := rank_unrank classes sizeOf sized distinct _ value decoded
      simp only [rankSigned, ranked, Option.map_some]
      have hs := Int.toNat_of_nonneg (show 0 ≤ size by omega)
      have hr := Int.toNat_of_nonneg (show 0 ≤ index by omega)
      simp only [hs, hr]

/-- A signed query has a member exactly at the nonnegative ranks below its count. -/
theorem unrankSigned_exists_iff (classes : Nat → List α) (size index : Int) :
    (∃ value, unrankSigned classes size index = some value) ↔
      0 ≤ index ∧ index.toNat < countSigned classes size := by
  by_cases negative : index < 0
  · simp [unrankSigned, negative, show ¬0 ≤ index by omega]
  · have nonnegative : 0 ≤ index := by omega
    simp only [unrankSigned, negative, ite_false, nonnegative, true_and, countSigned]
    constructor
    · rintro ⟨value, found⟩
      exact (List.getElem?_eq_some_iff.mp found).1
    · intro valid
      exact ⟨(termsSigned classes size)[index.toNat], List.getElem?_eq_getElem valid⟩

/-- A finite size-major prefix visits all classes through its bound. -/
def through (classes : Nat → List α) (bound : Nat) : List α :=
  (List.range (bound + 1)).flatMap classes

/-- Increasing the bound appends the entire next class. -/
theorem prefix_succ (classes : Nat → List α) (bound : Nat) :
    through classes (bound + 1) = through classes bound ++ classes (bound + 1) := by
  simp [through, List.range_succ, List.flatMap_append]

/-- Every member of a bounded prefix occurs at some size within the bound. -/
theorem mem_prefix (classes : Nat → List α) (bound : Nat) (value : α) :
    value ∈ through classes bound ↔ ∃ size, size ≤ bound ∧ value ∈ classes size := by
  simp only [through, List.mem_flatMap, List.mem_range]
  constructor <;> rintro ⟨size, inside, member⟩ <;> exact ⟨size, by omega, member⟩

/-- A bounded prefix contains precisely the valid members within its size bound. -/
theorem prefix_exact (classes : Nat → List α) (sizeOf : α → Nat) (valid : α → Prop)
    (exact : ∀ size value, value ∈ classes size ↔ valid value ∧ sizeOf value = size)
    (bound : Nat) (value : α) :
    value ∈ through classes bound ↔ valid value ∧ sizeOf value ≤ bound := by
  rw [mem_prefix]
  constructor
  · rintro ⟨size, within, member⟩
    obtain ⟨accepted, same⟩ := (exact size value).mp member
    exact ⟨accepted, by omega⟩
  · rintro ⟨accepted, within⟩
    exact ⟨sizeOf value, within, (exact _ _).mpr ⟨accepted, rfl⟩⟩

/-- Each accepted finite member appears at a finite bound. Empty classes cannot stop it. -/
theorem prefix_complete (classes : Nat → List α) (sizeOf : α → Nat) (valid : α → Prop)
    (exact : ∀ size value, value ∈ classes size ↔ valid value ∧ sizeOf value = size)
    (value : α) : (∃ bound, value ∈ through classes bound) ↔ valid value := by
  simp only [prefix_exact classes sizeOf valid exact]
  constructor
  · rintro ⟨_, accepted, _⟩; exact accepted
  · intro accepted; exact ⟨sizeOf value, accepted, Nat.le_refl _⟩

/-- A size-major rank is its class rank plus the counts at smaller sizes. -/
def offset (classes : Nat → List α) (size : Nat) : Nat :=
  ((List.range size).map fun n => count classes n).sum

/-- Every valid class position keeps its member at all larger prefix bounds. -/
theorem prefix_unrank (classes : Nat → List α) (bound : Nat) (position : Position)
    (within : position.size ≤ bound) (valid : position.rank < count classes position.size) :
    (through classes bound)[offset classes position.size + position.rank]? = unrank classes position :=
  RecursiveSize.get_class_offset classes bound position.size position.rank within valid

/-- Every prefix is ordered by nondecreasing member size. -/
theorem prefix_ordered (classes : Nat → List α) (sizeOf : α → Nat)
    (sized : Sized classes sizeOf) (bound : Nat) :
    (through classes bound).Pairwise (fun first second => sizeOf first ≤ sizeOf second) := by
  induction bound with
  | zero =>
      suffices (classes 0).Pairwise (fun first second => sizeOf first ≤ sizeOf second) by
        simpa [through] using this
      apply List.pairwise_of_forall_mem_list
      intro first firstMem second secondMem
      rw [sized 0 first firstMem, sized 0 second secondMem]
      exact Nat.le_refl _
  | succ bound ih =>
      rw [prefix_succ, List.pairwise_append]
      refine ⟨ih, ?_, ?_⟩
      · apply List.pairwise_of_forall_mem_list
        intro first firstMem second secondMem
        rw [sized _ first firstMem, sized _ second secondMem]
        exact Nat.le_refl _
      · intro first firstMem second secondMem
        obtain ⟨size, within, member⟩ := (mem_prefix classes bound first).mp firstMem
        rw [sized size first member, sized _ second secondMem]
        omega

/-- Distinct classes with their exact sizes have no duplicates across a prefix. -/
theorem prefix_nodup (classes : Nat → List α) (sizeOf : α → Nat)
    (sized : Sized classes sizeOf) (distinct : ∀ size, (classes size).Nodup) (bound : Nat) :
    (through classes bound).Nodup := by
  induction bound with
  | zero => simpa [through] using distinct 0
  | succ bound ih =>
      rw [prefix_succ, List.nodup_append]
      refine ⟨ih, distinct _, ?_⟩
      intro value firstMem other secondMem same
      subst other
      obtain ⟨size, within, member⟩ := (mem_prefix classes bound value).mp firstMem
      have first := sized size value member
      have second := sized _ value secondMem
      omega

end MicroCFTA.SourceSizedQueries
