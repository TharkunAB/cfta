import MicroCFTA.SourceSizedGroupedPreparedIndex
import MicroCFTA.SourceSizedDispatch

/-!
# Signed queries of successful grouped field observations

The source fromTable guard checks the signed rank and the class count.
It has no size guard. The termsFrom query visits the Integer ranks from
max 0 from through total minus one, in ascending order. It reads the same
independently computed count and selector fields.

The prepared signed count projects size.toNat to the checked natural-size
field observations. A negative request therefore has the proved zero-size
count. This is a count projection, not an added fromTable size guard.
Its correspondence with native sparse lookup at signed Integer sizes is
separate. Native sparse storage, lazy sharing, and cached sizedRank remain
separate. This module does not change the public Exact contract.
-/
namespace MicroCFTA.SourceSizedGroupedPublicQueries
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys

variable {Value State Symbol Formula : Type}

/-- Enumerate the literal source Integer rank interval, with unit rank steps. -/
def rankSteps (total : Nat) (start : Int) : List Int :=
  (List.range (total - start.toNat)).map fun (offset : Nat) => max 0 start + (offset : Int)

/-- The natural range representation retains the exact source signed starting rank. -/
theorem rankSteps_eq (total : Nat) (start : Int) :
    rankSteps total start = (List.range' start.toNat (total - start.toNat)).map Int.ofNat := by
  rw [rankSteps, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro offset _
  simp only [Function.comp_def, Int.ofNat_eq_natCast]
  omega

/-- Each source rank step is the starting rank plus its zero-based offset. -/
theorem rankSteps_at (total : Nat) (start : Int) (offset : Nat)
    (within : offset < total - start.toNat) :
    (rankSteps total start)[offset]? = some (max 0 start + (offset : Int)) := by
  simp only [rankSteps, List.getElem?_map, List.getElem?_range within, Option.map_some]

/-- The source rank interval contains exactly the requested in-class signed ranks. -/
theorem mem_rankSteps (total : Nat) (start rank : Int) :
    rank ∈ rankSteps total start ↔ max 0 start ≤ rank ∧ rank < (total : Int) := by
  rw [rankSteps_eq]
  have startCast : (start.toNat : Int) = max 0 start :=
    (Int.toNat_eq_max start).trans (Int.max_comm start 0)
  constructor
  · intro member
    obtain ⟨natural, present, same⟩ := List.mem_map.mp member
    change (natural : Int) = rank at same
    obtain ⟨offset, within, rankEq⟩ := List.mem_range'.mp present
    simp only [Nat.one_mul] at rankEq
    omega
  · rintro ⟨lower, upper⟩
    have nonnegative : 0 ≤ rank := by omega
    have rankCast := Int.toNat_of_nonneg nonnegative
    apply List.mem_map.mpr
    refine ⟨rank.toNat, ?_, rankCast⟩
    apply List.mem_range'.mpr
    exact ⟨rank.toNat - start.toNat, by omega, by omega⟩

/-- The literal fromTable rank guard precedes the independent raw selector read. -/
def unrankFields (count : Int → Nat) (select : Int → Nat → Option Value)
    (size rank : Int) : Option Value :=
  if 0 ≤ rank ∧ rank < (count size : Int) then select size rank.toNat else none

/-- The literal source comprehension selects each rank in its Integer interval. -/
def termsFromFields (count : Int → Nat) (select : Int → Nat → Option Value)
    (size start : Int) : List Value :=
  (rankSteps (count size) start).filterMap fun rank => unrankFields count select size rank

private theorem unrankFields_exact (count : Int → Nat) (select : Int → Nat → Option Value)
    (classes : Int → List Value)
    (counts : ∀ size, count size = (classes size).length)
    (selected : ∀ size rank, rank < count size → select size rank = (classes size)[rank]?)
    (size rank : Int) :
    unrankFields count select size rank = if 0 ≤ rank then (classes size)[rank.toNat]? else none := by
  by_cases nonnegative : 0 ≤ rank
  · by_cases within : rank < (count size : Int)
    · have bounded : rank.toNat < count size := by omega
      simp only [unrankFields, nonnegative, within, and_self, ite_true]
      exact selected size rank.toNat bounded
    · have outside : (classes size).length ≤ rank.toNat := by
        rw [← counts]
        omega
      simp [unrankFields, nonnegative, within, List.getElem?_eq_none outside]
  · simp [unrankFields, nonnegative]

private theorem range_select_drop (values : List Value) (start : Nat) :
    (List.range' start (values.length - start)).filterMap (fun rank => values[rank]?) = values.drop start := by
  rw [List.range'_eq_map_range, List.filterMap_map]
  simpa only [List.length_drop, List.getElem?_drop, Function.comp_def] using
    SourceSizedDispatch.range_select (values.drop start)

private theorem termsFromFields_exact (count : Int → Nat) (select : Int → Nat → Option Value)
    (classes : Int → List Value)
    (counts : ∀ size, count size = (classes size).length)
    (selected : ∀ size rank, rank < count size → select size rank = (classes size)[rank]?)
    (size start : Int) :
    termsFromFields count select size start = (classes size).drop start.toNat := by
  have naturalRead (rank : Nat) : unrankFields count select size (rank : Int) = (classes size)[rank]? := by
    simpa using unrankFields_exact count select classes counts selected size (rank : Int)
  unfold termsFromFields
  rw [rankSteps_eq]
  simp only [List.filterMap_map, Function.comp_def, Int.ofNat_eq_natCast, naturalRead, counts size]
  exact range_select_drop (classes size) start.toNat

section Prepared

variable [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]
  (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula)) (root : State)
  (output : SourceSizedConjunctionWorklist.Stored State Symbol)
  (success : SourceSizedConjunctionPreparation.prepare original root = some output)

/-- Extend the independently computed source count observations to signed request sizes. -/
def countAt (key : List State) (size : Int) : Nat :=
  SourceSizedGroupedPreparedIndex.countAt original root output success size.toNat key

/-- Read the raw source selector field; the public guard remains in unrankFields. -/
def rawSelect (key : List State) (size : Int) (rank : Nat) : Option (Term Symbol) :=
  let index := SourceSizedGroupedTableIndex.indexAt
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output) size.toNat key
  index.select ⟨size.toNat, rank⟩

/-- Execute the actual signed rank guard and then read the constructed selector field. -/
def unrankAt (key : List State) (size rank : Int) : Option (Term Symbol) :=
  unrankFields (countAt original root output success key) (rawSelect original root output success key) size rank

/-- Execute the actual signed rank interval and its guarded selector comprehension. -/
def termsFromAt (key : List State) (size start : Int) : List (Term Symbol) :=
  termsFromFields (countAt original root output success key) (rawSelect original root output success key) size start

/-- The signed count projection has the exact independently specified class length. -/
theorem countAt_eq (key : List State) (size : Int) :
    countAt original root output success key size =
      (SourceSizedGroupedClasses.classes (lookup output) size.toNat key).length :=
  SourceSizedGroupedPreparedIndex.countAt_eq original root output success size.toNat key

/-- A count-guarded raw read retains the checked source class position. -/
theorem rawSelect_eq (key : List State) (size : Int) (rank : Nat)
    (within : rank < countAt original root output success key size) :
    rawSelect original root output success key size rank =
      (SourceSizedGroupedClasses.classes (lookup output) size.toNat key)[rank]? :=
  SourceSizedGroupedTableIndex.evaluate_select (size.toNat + 1)
    (SourceSizedGroupedMinimumIndex.known original root output success) (lookup output)
    (SourceSizedGroupedPreparedIndex.missing_empty original root output success)
    size.toNat rank key (Nat.le_refl _) within

/-- The source signed selector agrees with the ordered class without an extra size guard. -/
theorem unrankAt_eq (key : List State) (size rank : Int) :
    unrankAt original root output success key size rank =
      if 0 ≤ rank then (SourceSizedGroupedClasses.classes (lookup output) size.toNat key)[rank.toNat]? else none :=
  unrankFields_exact _ _ _ (countAt_eq original root output success key) (rawSelect_eq original root output success key)
    size rank

/-- Natural sizes and ranks retain the exact checked source class position. -/
theorem unrankAt_nat (key : List State) (size rank : Nat) :
    unrankAt original root output success key (size : Int) (rank : Int) =
      (SourceSizedGroupedClasses.classes (lookup output) size key)[rank]? := by
  simpa using unrankAt_eq original root output success key (size : Int) (rank : Int)

/-- A negative class rank is rejected before the raw source field is read. -/
theorem unrankAt_negative_rank (key : List State) (size rank : Int) (negative : rank < 0) :
    unrankAt original root output success key size rank = none := by
  rw [unrankAt_eq]
  simp only [show ¬0 ≤ rank by omega, ite_false]

/-- The literal signed count guard rejects exactly the out-of-class ranks. -/
theorem unrankAt_none_iff (key : List State) (size rank : Int) :
    unrankAt original root output success key size rank = none ↔
      rank < 0 ∨ (countAt original root output success key size : Int) ≤ rank := by
  rw [unrankAt_eq]
  by_cases nonnegative : 0 ≤ rank
  · simp only [nonnegative, ite_true, List.getElem?_eq_none_iff]
    have counts := countAt_eq original root output success key size
    omega
  · have negative : rank < 0 := by omega
    simp [nonnegative, negative]

/-- Nonpositive request sizes have zero count in the signed count projection. -/
theorem countAt_nonpositive (key : List State) (size : Int) (nonpositive : size ≤ 0) :
    countAt original root output success key size = 0 := by
  have zero : size.toNat = 0 := Int.toNat_eq_zero.mpr nonpositive
  rw [countAt_eq, zero, SourceSizedGroupedClasses.classes_zero]
  rfl

/-- A nonpositive size is rejected because its proved count is zero. -/
theorem unrankAt_nonpositive (key : List State) (size rank : Int) (nonpositive : size ≤ 0) :
    unrankAt original root output success key size rank = none := by
  rw [unrankAt_none_iff, countAt_nonpositive original root output success key size nonpositive]
  omega

/-- Literal source rank stepping reconstructs the exact ordered class suffix. -/
theorem termsFromAt_eq (key : List State) (size start : Int) :
    termsFromAt original root output success key size start =
      (SourceSizedGroupedClasses.classes (lookup output) size.toNat key).drop start.toNat :=
  termsFromFields_exact _ _ _ (countAt_eq original root output success key) (rawSelect_eq original root output success key)
    size start

/-- Natural request sizes and starting ranks preserve the exact ordered suffix. -/
theorem termsFromAt_nat (key : List State) (size start : Nat) :
    termsFromAt original root output success key (size : Int) (start : Int) =
      (SourceSizedGroupedClasses.classes (lookup output) size key).drop start := by
  simpa using termsFromAt_eq original root output success key (size : Int) (start : Int)

/-- A nonpositive starting rank gives the whole source size class. -/
theorem termsFromAt_nonpositive_start (key : List State) (size start : Int) (nonpositive : start ≤ 0) :
    termsFromAt original root output success key size start =
      SourceSizedGroupedClasses.classes (lookup output) size.toNat key := by
  rw [termsFromAt_eq, Int.toNat_eq_zero.mpr nonpositive]
  rfl

/-- The source suffix length is the remaining count after the starting rank. -/
theorem termsFromAt_length (key : List State) (size start : Int) :
    (termsFromAt original root output success key size start).length =
      countAt original root output success key size - start.toNat := by
  rw [termsFromAt_eq, List.length_drop, countAt_eq]

/-- Nonpositive sizes have an empty suffix because their class count is zero. -/
theorem termsFromAt_nonpositive (key : List State) (size start : Int) (nonpositive : size ≤ 0) :
    termsFromAt original root output success key size start = [] := by
  apply List.length_eq_zero_iff.mp
  rw [termsFromAt_length, countAt_nonpositive original root output success key size nonpositive]
  exact Nat.zero_sub _

/-- Starting at or above the signed source count gives an empty rank interval. -/
theorem termsFromAt_outside (key : List State) (size start : Int)
    (outside : (countAt original root output success key size : Int) ≤ start) :
    termsFromAt original root output success key size start = [] := by
  apply List.length_eq_zero_iff.mp
  rw [termsFromAt_length]
  omega

end Prepared
end MicroCFTA.SourceSizedGroupedPublicQueries
