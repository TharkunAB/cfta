import MicroCFTA.SourceSizedGroupedSparseFields

/-!
# The source sparse product decoder

`blocks` and `split` follow `Ranked/Internal/Size.hs:765-784`. The source
reads the stored left-size prefix, subtracts its weighted block counts, and
then uses quotient and remainder. `none` models the source error branch.

Omitted sizes and stored zero counts do not change selection. A bounded
product rank gives two bounded component ranks and a positive divisor.
These statements concern finite natural count lists. Machine `Int`
conversions, signed invalid arguments, and lazy prefix productivity remain
separate.
-/
namespace MicroCFTA.SourceSizedSparseProductSplit

open Sparse (Series Ordered coefficient valueAtSize)
open SizedRank (Position Valid sizeClassOf sizeMajorRank countBelow splitCounts)
open RecursiveJoinFields (convolve)

private theorem lookup_mem (series : Series Nat) (ordered : Ordered series)
    (size count : Nat) (member : (size, count) ∈ series) :
    valueAtSize series size = count := by
  induction series with
  | nil => cases member
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp member with same | later
    · have keys : size = key := congrArg Prod.fst same
      have values : count = value := congrArg Prod.snd same
      subst size
      subst count
      simp [valueAtSize]
    · have before : key < size := headBefore _ later
      simpa only [valueAtSize, before, ite_true] using ih tailOrdered later

private theorem valid_of_lookup (series : Series Nat) (position : Position)
    (within : position.rank < valueAtSize series position.size) : Valid series position := by
  induction series with
  | nil => simp only [valueAtSize] at within; omega
  | cons entry rest ih =>
    rcases entry with ⟨key, count⟩
    by_cases before : key < position.size
    · have tail : position.rank < valueAtSize rest position.size := by
        simpa only [valueAtSize, before, ite_true] using within
      obtain ⟨value, member, bounded⟩ := ih tail
      exact ⟨value, List.mem_cons_of_mem _ member, bounded⟩
    · by_cases same : key = position.size
      · have bounded : position.rank < count := by
          simpa only [valueAtSize, ite_eq_right before, ite_eq_left same] using within
        exact ⟨count, by simp [same], bounded⟩
      · have impossible : position.rank < 0 := by
          simpa only [valueAtSize, before, ite_false, same] using within
        omega

/-- Ordered lookup gives exactly the valid stored class interval. -/
theorem valid_iff_lookup (series : Series Nat) (ordered : Ordered series) (position : Position) :
    Valid series position ↔ position.rank < valueAtSize series position.size := by
  constructor
  · rintro ⟨count, member, bounded⟩
    rw [lookup_mem series ordered position.size count member]
    exact bounded
  · exact valid_of_lookup series position

/-- The class prefix depends only on the count lookup at each smaller size. -/
theorem countBelow_lookup (series : Series Nat) (ordered : Ordered series) (size : Nat) :
    countBelow series size = ((List.range size).map (valueAtSize series)).sum := by
  have weighted := SizedRank.weighted_coefficient_sum series size (fun _ => 1)
  rw [SizedRank.filter_lt_eq_takeWhile series ordered size] at weighted
  simp only [Nat.mul_one] at weighted
  calc
    countBelow series size =
        ((series.takeWhile (fun entry => decide (entry.1 < size))).map Prod.snd).sum :=
      SizedRank.countBelow_takeWhile series size
    _ = ((List.range size).map (coefficient series)).sum := weighted.symm
    _ = ((List.range size).map (valueAtSize series)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro key _
      exact (Sparse.valueAtSize_correct series ordered key).symm

private theorem select_of_lookup (first second : Series Nat)
    (firstOrdered : Ordered first) (secondOrdered : Ordered second)
    (same : ∀ size, valueAtSize first size = valueAtSize second size)
    (rank : Nat) (position : Position) (found : sizeClassOf first rank = some position) :
    sizeClassOf second rank = some position := by
  have validFirst := SizedRank.sizeClassOf_valid first rank position found
  have boundedFirst := (valid_iff_lookup first firstOrdered position).mp validFirst
  have validSecond : Valid second position :=
    (valid_iff_lookup second secondOrdered position).mpr (by
      rw [← same]
      exact boundedFirst)
  have offset : countBelow first position.size = countBelow second position.size := by
    rw [countBelow_lookup first firstOrdered, countBelow_lookup second secondOrdered]
    apply congrArg List.sum
    apply List.map_congr_left
    intro size _
    exact same size
  have oldRank := SizedRank.sizeMajorRank_sizeClassOf first firstOrdered rank position found
  have newRank : sizeMajorRank second position = rank := by
    unfold sizeMajorRank at oldRank ⊢
    rw [← offset]
    exact oldRank
  have selected := SizedRank.sizeClassOf_sizeMajorRank second secondOrdered position validSecond
  rwa [newRank] at selected

/-- Extra zero classes and omitted zero sizes preserve the entire selector. -/
theorem sizeClassOf_eq_of_lookup (first second : Series Nat)
    (firstOrdered : Ordered first) (secondOrdered : Ordered second)
    (same : ∀ size, valueAtSize first size = valueAtSize second size) (rank : Nat) :
    sizeClassOf first rank = sizeClassOf second rank := by
  cases firstRun : sizeClassOf first rank with
  | none =>
    cases secondRun : sizeClassOf second rank with
    | none => rfl
    | some position =>
      have other := select_of_lookup second first secondOrdered firstOrdered
        (fun size => (same size).symm) rank position secondRun
      have impossible : (none : Option Position) = some position := firstRun.symm.trans other
      cases impossible
  | some position =>
    exact (select_of_lookup first second firstOrdered secondOrdered same rank position firstRun).symm

private theorem lookup_weighted (series : Series Nat) (weight : Nat → Nat) (size : Nat) :
    valueAtSize (series.map (fun entry => (entry.1, entry.2 * weight entry.1))) size =
      valueAtSize series size * weight size := by
  induction series with
  | nil => simp [valueAtSize]
  | cons entry rest ih =>
    rcases entry with ⟨key, count⟩
    simp only [List.map_cons, valueAtSize]
    by_cases before : key < size
    · simp only [ite_eq_left before, ih]
    · by_cases same : key = size
      · subst key
        simp
      · simp only [ite_eq_right before, ite_eq_right same, Nat.zero_mul]

private theorem lookup_takeWhile (series : Series Nat) (bound size : Nat) :
    valueAtSize (series.takeWhile (fun entry => decide (entry.1 ≤ bound))) size =
      if size ≤ bound then valueAtSize series size else 0 := by
  induction series with
  | nil => simp [valueAtSize]
  | cons entry rest ih =>
    rcases entry with ⟨key, count⟩
    by_cases kept : key ≤ bound
    · by_cases inside : size ≤ bound
      · simp [kept, inside, valueAtSize, ih]
      · have before : key < size := by omega
        simp [kept, inside, before, valueAtSize, ih]
    · by_cases inside : size ≤ bound
      · have before : ¬key < size := by omega
        have different : key ≠ size := by omega
        simp [kept, inside, before, different, valueAtSize]
      · simp [kept, inside, valueAtSize]

private theorem coefficient_map (keys : List Nat) (counts : Nat → Nat) (size : Nat) :
    coefficient (keys.map (fun key => (key, counts key))) size =
      (keys.map (fun key => if key = size then counts size else 0)).sum := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.map_cons, List.sum_cons, coefficient, ih]
    by_cases same : key = size <;> simp [same]

private theorem lookup_splitCounts (left right : Nat → Nat) (total size : Nat) :
    valueAtSize (splitCounts left right total) size =
      if size ≤ total then left size * right (total - size) else 0 := by
  rw [Sparse.valueAtSize_correct _ (SizedRank.splitCounts_ordered left right total)]
  unfold splitCounts
  rw [coefficient_map]
  simpa only [Nat.mul_one, eq_comm, Nat.lt_succ_iff] using
    SizedRank.sum_point (total + 1) size (left size * right (total - size)) (fun _ => 1)

/-- The exact stored prefix and weighted blocks visited by the native decoder. -/
def blocks (left right : Series Nat) (total : Nat) : Series Nat :=
  (left.takeWhile (fun entry => decide (entry.1 ≤ total))).map
    (fun entry => (entry.1, entry.2 * valueAtSize right (total - entry.1)))

/-- Block weighting and the source cutoff preserve the strict order of stored sizes. -/
theorem blocks_ordered (left right : Series Nat) (ordered : Ordered left) (total : Nat) :
    Ordered (blocks left right total) := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.sublist (List.takeWhile_sublist _) ordered

/-- The literal sparse prefix has the dense split table's count at every size. -/
theorem blocks_lookup (left right : Series Nat) (total size : Nat) :
    valueAtSize (blocks left right total) size =
      if size ≤ total then valueAtSize left size * valueAtSize right (total - size) else 0 := by
  unfold blocks
  rw [lookup_weighted (left.takeWhile (fun entry => decide (entry.1 ≤ total)))
    (fun childSize => valueAtSize right (total - childSize)) size,
    lookup_takeWhile left total size]
  by_cases inside : size ≤ total <;> simp [inside]

/-- Subtract source block counts, then decode the selected mixed-radix rank. -/
def split (left right : Series Nat) (position : Position) : Option (Position × Position) := do
  let block ← sizeClassOf (blocks left right position.size) position.rank
  let ranks := Probability.splitRank (valueAtSize right (position.size - block.size)) block.rank
  pure (⟨block.size, ranks.1⟩, ⟨position.size - block.size, ranks.2⟩)

/-- Literal sparse decoding equals dense decoding, including every out-of-range rank. -/
theorem split_eq (left right : Series Nat) (ordered : Ordered left) (position : Position) :
    split left right position = SizedRank.productSplit (valueAtSize left) (valueAtSize right) position := by
  unfold split SizedRank.productSplit
  rw [sizeClassOf_eq_of_lookup _ _ (blocks_ordered left right ordered position.size)
    (SizedRank.splitCounts_ordered (valueAtSize left) (valueAtSize right) position.size)
    (fun size => by rw [blocks_lookup, lookup_splitCounts])]

/-- Native sparse decoding recovers every valid encoded pair. -/
theorem split_position (left right : Series Nat) (ordered : Ordered left)
    (first second : Position)
    (firstValid : first.rank < valueAtSize left first.size)
    (secondValid : second.rank < valueAtSize right second.size) :
    split left right (SizedRank.sparseProductPosition left right first second) = some (first, second) := by
  rw [split_eq left right ordered, SizedRank.sparseProductPosition_correct left right ordered]
  exact SizedRank.productSplit_productPosition _ _ first second firstValid secondValid

/-- Re-encoding any returned sparse split recovers the original position. -/
theorem position_split (left right : Series Nat) (ordered : Ordered left)
    (position first second : Position) (found : split left right position = some (first, second)) :
    SizedRank.sparseProductPosition left right first second = position := by
  rw [SizedRank.sparseProductPosition_correct left right ordered]
  apply SizedRank.productPosition_productSplit _ _ position first second
  rw [← split_eq left right ordered]
  exact found

/-- A count-bounded request cannot reach the native error or divide by zero. -/
theorem split_complete (left right : Series Nat) (ordered : Ordered left) (position : Position)
    (bounded : position.rank < convolve (valueAtSize left) (valueAtSize right) position.size) :
    ∃ first second, split left right position = some (first, second) ∧
      first.size + second.size = position.size ∧
      first.rank < valueAtSize left first.size ∧ second.rank < valueAtSize right second.size ∧
      0 < valueAtSize right second.size := by
  obtain ⟨first, second, encoded, firstBound, secondBound⟩ :=
    RecursiveCallbackTables.product_split (valueAtSize left) (valueAtSize right) position bounded
  refine ⟨first, second, ?_, ?_, firstBound, secondBound, ?_⟩
  · rw [split_eq left right ordered, ← encoded]
    exact SizedRank.productSplit_productPosition _ _ first second firstBound secondBound
  · exact congrArg Position.size encoded
  · omega

/-- The actual finite sparse product count supplies the decoder's bound. -/
theorem split_complete_product (left right : Series Nat)
    (leftOrdered : Ordered left) (rightOrdered : Ordered right) (position : Position)
    (bounded : position.rank < valueAtSize (Sparse.mulSparse left right) position.size) :
    ∃ first second, split left right position = some (first, second) ∧
      first.size + second.size = position.size ∧
      first.rank < valueAtSize left first.size ∧ second.rank < valueAtSize right second.size ∧
      0 < valueAtSize right second.size := by
  have count : valueAtSize (Sparse.mulSparse left right) position.size =
      convolve (valueAtSize left) (valueAtSize right) position.size := by
    rw [Sparse.valueAtSize_mulSparse left right leftOrdered rightOrdered,
      SourceSizedGroupedSparseFields.convolution_eq_convolve]
    have first : coefficient left = valueAtSize left :=
      funext (fun size => (Sparse.valueAtSize_correct left leftOrdered size).symm)
    have second : coefficient right = valueAtSize right :=
      funext (fun size => (Sparse.valueAtSize_correct right rightOrdered size).symm)
    rw [first, second]
  exact split_complete left right leftOrdered position (by rw [← count]; exact bounded)

end MicroCFTA.SourceSizedSparseProductSplit
