import MicroCFTA.FiniteSizeSampling
import MicroCFTA.FiniteSum

/-!
# Finite retained mass series

The source omits empty sizes. Lookup, product convolution, and sums operate on
the same finite class masses as the source sampler fields.
-/
namespace MicroCFTA.FiniteSizeSeries
open Probability SourcePlanPositions SizeMass FiniteSizeFields FiniteSizeSampling

/-- Actual finite class-table keys, in ascending order, with empty classes omitted. -/
def sizes (record : Record) : List Nat :=
  (List.range (SourcePlanPartition.maxSize record.plan + 1)).filter
    (fun size => !(classRanks record.plan size).isEmpty)

/-- Store the derived source mass only at sizes with members. -/
def series (record : Record) : Sparse.Series Rat :=
  (sizes record).map (fun size => (size, massAt record size))

theorem sizes_distinct (record : Record) : (sizes record).Nodup := List.nodup_range.filter _

theorem sizes_ordered (record : Record) : (sizes record).Pairwise (· < ·) :=
  (RecursiveSize.range_ordered _).filter _

theorem series_ordered (record : Record) : Sparse.Ordered (series record) := by
  exact List.pairwise_map.mpr (sizes_ordered record)

/-- The structural finite plan bound contains every live class. -/
theorem sizes_exact (record : Record) (size : Nat) : size ∈ sizes record ↔ classRanks record.plan size ≠ [] := by
  simp only [sizes, List.mem_filter, List.mem_range]
  constructor
  · intro both empty
    simp [empty] at both
  · intro nonempty
    obtain ⟨rank, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have bound := SourcePlanPartition.class_size_bound record.plan size rank present
    exact ⟨by omega, by simp [List.isEmpty_eq_false_iff.mpr nonempty]⟩

/-- Finite class masses have no contribution at a size omitted from the table. -/
theorem missing_mass (record : Record) (valid : Valid record) (size : Nat) (missing : size ∉ sizes record) :
    massAt record size = 0 := by
  have empty : classRanks record.plan size = [] := by
    by_cases empty : classRanks record.plan size = []
    · exact empty
    · exact False.elim (missing ((sizes_exact record size).mpr empty))
  simpa [empty] using valid.mass size

/-- Coefficient lookup on a distinct table reads exactly its one matching stored value. -/
theorem coefficient_table (keys : List Nat) (unique : keys.Nodup) (value : Nat → Rat) (wanted : Nat) :
    Sparse.coefficient (keys.map (fun size => (size, value size))) wanted =
      if wanted ∈ keys then value wanted else 0 := by
  have expands : Sparse.coefficient (keys.map (fun size => (size, value size))) wanted =
      FiniteSum.listSum keys (fun size => if size = wanted then value wanted else 0) := by
    clear unique
    induction keys with
    | nil => rfl
    | cons size rest ih =>
        simp only [List.map_cons, Sparse.coefficient, FiniteSum.listSum, ih]
        by_cases same : size = wanted <;> simp [same]
  rw [expands]
  exact FiniteSum.listSum_single keys unique wanted (value wanted)

/-- The constructed table stores the same masses that choose size branches. -/
theorem series_coefficient (record : Record) (valid : Valid record) (size : Nat) :
    Sparse.coefficient (series record) size = massAt record size := by
  rw [series, coefficient_table _ (sizes_distinct record)]
  by_cases present : size ∈ sizes record
  · simp [present]
  · simp [present, missing_mass record valid size present]

/-- The actual source's early-stop sparse lookup agrees with the complete class mass. -/
theorem series_lookup (record : Record) (valid : Valid record) (size : Nat) :
    Sparse.valueAtSize (series record) size = massAt record size := by
  rw [Sparse.valueAtSize_correct _ (series_ordered record), series_coefficient record valid]

/-- Expand the exact source finite convolution loop in its stored left-size order. -/
theorem splitSum_table (keys : List Nat) (value : Nat → Rat) (right : Sparse.Series Rat) (wanted : Nat) :
    Sparse.splitSum (keys.map (fun size => (size, value size))) right wanted =
      FiniteSum.listSum keys (fun size => if size ≤ wanted then value size * Sparse.coefficient right (wanted - size) else 0) := by
  induction keys with
  | nil => rfl
  | cons size rest ih => simp [Sparse.splitSum, FiniteSum.listSum, ih]

/-- The complete product mass is independent of omitted empty classes and includes the zero split. -/
theorem pair_sparse_lookup (left right : Record) (leftValid : Valid left) (rightValid : Valid right) (size : Nat) :
    Sparse.valueAtSize (Sparse.mulSparse (series left) (series right)) size =
      ((List.range (size + 1)).map (fun split => massAt left split * massAt right (size - split))).sum := by
  rw [Sparse.sparse_split_correct _ _ (series_ordered left) (series_ordered right)]
  unfold series
  rw [splitSum_table]
  have rightCoefficient : ∀ split,
      Sparse.coefficient ((sizes right).map (fun size => (size, massAt right size))) (size - split) =
        massAt right (size - split) := fun split => series_coefficient right rightValid _
  simp only [rightCoefficient]
  let value := fun split => if split ≤ size then massAt left split * massAt right (size - split) else 0
  have supported : FiniteSum.HasSum value (FiniteSum.listSum (sizes left) value) := by
    refine ⟨sizes left, sizes_distinct left, ?_, rfl⟩
    intro split nonzero
    by_cases present : split ∈ sizes left
    · exact present
    · have zero := missing_mass left leftValid split present
      simp [value, zero] at nonzero
  have sum := FiniteSum.of_cover supported (List.range (size + 1)) List.nodup_range (by
    intro split nonzero
    have bound : split ≤ size := by
      by_cases bound : split ≤ size
      · exact bound
      · simp [value, bound] at nonzero
    exact List.mem_range.mpr (by omega))
  change FiniteSum.listSum (sizes left) value = _
  rw [← sum]
  rw [← FiniteSum.listSum_eq]
  apply FiniteSum.listSum_congr
  intro split present
  have bound := List.mem_range.mp present
  simp [value, show split ≤ size by omega]

/-- Actual pairMassIndex lookup equals the retained field of the source pair record. -/
theorem pair_mass_record (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (retained : (left.retained.isSome || right.retained.isSome) = true) (size : Nat) :
    Sparse.valueAtSize (Sparse.mulSparse (series left) (series right)) size = massAt (sourcePair left right) size := by
  rw [pair_sparse_lookup left right leftValid rightValid, pair_retained_mass left right leftValid rightValid retained]

/-- Source sumMassIndexes follows the same right fold over addSparse. -/
def sumSeries (records : List Record) : Sparse.Series Rat :=
  records.foldr (fun record rest => Sparse.addSparse (series record) rest) []

theorem sumSeries_ordered (records : List Record) : Sparse.Ordered (sumSeries records) := by
  induction records with
  | nil => simp [sumSeries, Sparse.Ordered]
  | cons record rest ih => exact Sparse.addSparse_ordered _ _ (series_ordered record) ih

/-- Actual sumMassIndexes lookup equals the derived sum of child class masses. -/
theorem sumSeries_lookup (records : List Record) (valid : ∀ record ∈ records, Valid record) (size : Nat) :
    Sparse.valueAtSize (sumSeries records) size = (records.map (fun record => massAt record size)).sum := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      change Sparse.valueAtSize (Sparse.addSparse (series record) (sumSeries rest)) size = _
      rw [Sparse.valueAtSize_addSparse _ _ (series_ordered record) (sumSeries_ordered rest),
        series_lookup record (valid record (by simp)), ih (fun record member => valid record (by simp [member]))]
      rfl

/-- Actual choice mass metadata equals the field consumed by its class sampler. -/
theorem choice_mass_record (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (retained : records.any (fun record => record.retained.isSome) = true) (size : Nat) :
    Sparse.valueAtSize (sumSeries records) size = massAt (choice records) size := by
  rw [sumSeries_lookup records valid, choice_retained_mass records valid retained]


/-- A stored source mass table can use any ordered representation with the correct finite coefficients. -/
def Matches (record : Record) (stored : Sparse.Series Rat) : Prop :=
  Sparse.Ordered stored ∧ ∀ size, Sparse.coefficient stored size = massAt record size

theorem canonical_matches (record : Record) (valid : Valid record) : Matches record (series record) :=
  ⟨series_ordered record, series_coefficient record valid⟩

/-- Expand source convolution into its independent finite Cartesian sum. -/
theorem convolution_cartesian (left right : Sparse.Series Rat) (size : Nat) :
    Sparse.convolution left right size = FiniteSum.listSum left (fun first =>
      FiniteSum.listSum right (fun second =>
        if first.1 + second.1 = size then first.2 * second.2 else 0)) := by
  have shifted : ∀ (first : Nat × Rat) (right : Sparse.Series Rat),
      Sparse.coefficient (Sparse.shiftScale first.1 first.2 right) size =
        FiniteSum.listSum right (fun second => if first.1 + second.1 = size then first.2 * second.2 else 0) := by
    intro first right
    induction right with
    | nil => rfl
    | cons second rest ih =>
        change (if first.1 + second.1 = size then first.2 * second.2 else 0) +
          Sparse.coefficient (Sparse.shiftScale first.1 first.2 rest) size = _
        rw [ih]
        rfl
  induction left with
  | nil => rfl
  | cons first rest ih => rw [Sparse.convolution, shifted, FiniteSum.listSum, ih]

/-- Source sparse product coefficients are commutative even when the stored rows differ. -/
theorem product_coeff_comm (left right : Sparse.Series Rat) (size : Nat) :
    Sparse.coefficient (Sparse.mulSparse left right) size = Sparse.coefficient (Sparse.mulSparse right left) size := by
  rw [Sparse.coefficient_mulSparse, Sparse.coefficient_mulSparse, convolution_cartesian,
    convolution_cartesian, FiniteSum.listSum_exchange]
  apply FiniteSum.listSum_congr
  intro second member
  apply FiniteSum.listSum_congr
  intro first present
  simp only [Nat.add_comm first.1 second.1, Rat.mul_comm first.2 second.2]

/-- The source product depends on the right mass function, not its sparse row representation. -/
theorem product_coeff_right (left first second : Sparse.Series Rat)
    (same : ∀ size, Sparse.coefficient first size = Sparse.coefficient second size) (size : Nat) :
    Sparse.coefficient (Sparse.mulSparse left first) size = Sparse.coefficient (Sparse.mulSparse left second) size := by
  rw [Sparse.coefficient_mulSparse, Sparse.coefficient_mulSparse,
    Sparse.convolution_eq_splitSum, Sparse.convolution_eq_splitSum]
  induction left with
  | nil => rfl
  | cons entry rest ih => simp [Sparse.splitSum, same, ih]

/-- Both sparse operand representations can change without changing any product mass. -/
theorem product_coeff_congr (left right first second : Sparse.Series Rat)
    (sameLeft : ∀ size, Sparse.coefficient left size = Sparse.coefficient first size)
    (sameRight : ∀ size, Sparse.coefficient right size = Sparse.coefficient second size) (size : Nat) :
    Sparse.coefficient (Sparse.mulSparse left right) size = Sparse.coefficient (Sparse.mulSparse first second) size := by
  rw [product_coeff_right left right second sameRight, product_coeff_comm left second,
    product_coeff_right second left first sameLeft, product_coeff_comm second first]

/-- The actual pairMassIndex operation preserves the field invariant for the stored input tables. -/
theorem pair_matches (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (leftRows rightRows : Sparse.Series Rat) (leftMatch : Matches left leftRows) (rightMatch : Matches right rightRows)
    (retained : (left.retained.isSome || right.retained.isSome) = true) :
    Matches (sourcePair left right) (Sparse.mulSparse leftRows rightRows) := by
  refine ⟨Sparse.mulSparse_ordered _ _ leftMatch.1 rightMatch.1, ?_⟩
  intro size
  rw [product_coeff_congr leftRows rightRows (series left) (series right)
    (fun size => (leftMatch.2 size).trans (series_coefficient left leftValid size).symm)
    (fun size => (rightMatch.2 size).trans (series_coefficient right rightValid size).symm)]
  rw [← Sparse.valueAtSize_correct _ (Sparse.mulSparse_ordered _ _ (series_ordered left) (series_ordered right)),
    pair_mass_record left right leftValid rightValid retained]

/-- The source's right-folded sum can retain the tables built by preceding constructors. -/
def sumStored (tables : List (Sparse.Series Rat)) : Sparse.Series Rat := tables.foldr Sparse.addSparse []

theorem sumStored_coeff (tables : List (Sparse.Series Rat)) (size : Nat) :
    Sparse.coefficient (sumStored tables) size = (tables.map (fun table => Sparse.coefficient table size)).sum := by
  induction tables with
  | nil => rfl
  | cons table rest ih => rw [sumStored, List.foldr_cons, Sparse.coefficient_addSparse, ← sumStored, ih]; rfl

theorem sumStored_ordered (tables : List (Sparse.Series Rat)) (ordered : ∀ table ∈ tables, Sparse.Ordered table) :
    Sparse.Ordered (sumStored tables) := by
  induction tables with
  | nil => simp [sumStored, Sparse.Ordered]
  | cons table rest ih =>
      exact Sparse.addSparse_ordered _ _ (ordered table (by simp)) (ih (fun table member => ordered table (by simp [member])))

/-- Actual sumMassIndexes also composes without rebuilding any previous table. -/
theorem choice_matches (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (stored : Record → Sparse.Series Rat) (coherent : ∀ record ∈ records, Matches record (stored record))
    (retained : records.any (fun record => record.retained.isSome) = true) :
    Matches (choice records) (sumStored (records.map stored)) := by
  constructor
  · apply sumStored_ordered
    intro table member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (coherent record present).1
  · intro size
    rw [sumStored_coeff, choice_retained_mass records valid retained]
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro record member
    exact (coherent record member).2 size


/-- A rebuilt observed member initializes its retained table from the actual source weight. -/
theorem observed_matches (size : Nat) (weight : Rat) : Matches (observed size weight) [(size, weight)] := by
  constructor
  · simp [Sparse.Ordered]
  · intro found
    simp [observed, massAt, Sparse.coefficient, Eq.comm, Rat.add_zero]

/-- Pure, hole, and resized indexed sources initialize their one finite size row. -/
theorem fixed_matches (size total : Nat) : Matches (uniform (fixedPlan size total)) [(size, (total : Rat))] := by
  constructor
  · simp [Sparse.Ordered]
  · intro found
    by_cases same : found = size
    · subst found; simp [uniform, massAt, fixedPlan_classes, Sparse.coefficient, Rat.add_zero]
    · simp [uniform, massAt, fixedPlan_classes, Sparse.coefficient, same, Ne.symm same, Rat.add_zero]

/-- Source finite payMassIndex shifts the stored rows and the class fields together. -/
theorem pay_matches (record : Record) (stored : Sparse.Series Rat) (coherent : Matches record stored) :
    Matches (pay record) (SizeTransport.payMasses stored) := by
  constructor
  · apply List.pairwise_map.mpr
    apply coherent.1.imp
    intro left right earlier
    change left.1 + 1 < right.1 + 1
    omega
  · intro size
    cases size with
    | zero => rw [SizeTransport.coefficient_pay_zero, pay_mass_zero]
    | succ size => rw [SizeTransport.coefficient_pay, coherent.2, pay_mass]

/-- The actual fallback countMassIndex stores the current structural class counts. -/
def countTable (record : Record) : Sparse.Series Rat :=
  (sizes record).map (fun size => (size, ((classRanks record.plan size).length : Rat)))

theorem countTable_matches (record : Record) (valid : Valid record) (absent : record.retained = none) :
    Matches record (countTable record) := by
  have same : countTable record = series record := by simp [countTable, series, massAt, absent]
  rw [same]
  exact canonical_matches record valid

end MicroCFTA.FiniteSizeSeries


