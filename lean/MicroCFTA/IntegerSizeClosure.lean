import MicroCFTA.FiniteSizeSeries

/-!
# Integer closure size fields

pointsStatic applies the open source to one fixed-size indexed point source.
The right rank varies fastest. closedMasses uses that same point count and
the number of integer variables as its size.
-/
namespace MicroCFTA.IntegerSizeClosure
open Probability SourcePlanPositions SizeMass FiniteSizeFields FiniteSizeSampling

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- A finite ordered scan with one possible nonempty branch executes that branch exactly once. -/
theorem flatMap_one [DecidableEq Key] (items : List Key) (unique : items.Nodup) (chosen : Key)
    (values : Key → List Item) (only : ∀ key ∈ items, key ≠ chosen → values key = []) :
    items.flatMap values = if chosen ∈ items then values chosen else [] := by
  induction items with
  | nil => simp
  | cons key rest ih =>
      have facts := List.nodup_cons.mp unique
      rw [List.flatMap_cons, ih facts.2 (fun key member => only key (by simp [member]))]
      by_cases same : key = chosen
      · subst key; simp [facts.1]
      · rw [only key (by simp) same]
        simp [Ne.symm same]

/-- A resized indexed point source has uniform size weights at exactly its tuple width. -/
def points (width pointCount : Nat) : Record := uniform (fixedPlan width pointCount)

theorem points_valid (width pointCount : Nat) : Valid (points width pointCount) := uniform_valid _

theorem points_weights (width pointCount size : Nat) :
    (points width pointCount).weights size = if size = width then counting (List.range pointCount) else [] := by
  simp only [points, uniform, fixedPlan_classes]
  split <;> rfl

theorem points_mass (width pointCount size : Nat) :
    massAt (points width pointCount) size = if size = width then (pointCount : Rat) else 0 := by
  by_cases same : size = width <;> simp [points, uniform, massAt, fixedPlan_classes, same]

/-- The right fixed-size record is either absent or one concrete uniform group. -/
theorem points_groups (width pointCount size : Nat) :
    liveGroup (points width pointCount) size =
      if size = width ∧ pointCount ≠ 0 then [⟨pointCount, counting (List.range pointCount)⟩] else [] := by
  by_cases same : size = width <;> by_cases zero : pointCount = 0 <;>
    simp [liveGroup, points_weights, same, zero, classGroup, points_mass, counting]

/-- Source closePoints adds the width to every original member size. -/
def close (width pointCount : Nat) (record : Record) : Record := pair record (points width pointCount)

theorem close_valid (width pointCount : Nat) (record : Record) (valid : Valid record) :
    Valid (close width pointCount record) := pair_valid record _ valid (points_valid width pointCount)

/-- Every nonempty product split uses exactly the original size remaining after the point width. -/
theorem close_groups (width pointCount : Nat) (record : Record) (size : Nat) :
    pairGroups record (points width pointCount) size =
      if width ≤ size ∧ pointCount ≠ 0 then
        (liveGroup record (size - width)).map (fun group =>
          ⟨group.mass * pointCount,
            Probability.map (fun ranks => pairRank pointCount ranks.1 ranks.2)
              (Probability.product group.weights (counting (List.range pointCount)))⟩)
      else [] := by
  unfold pairGroups
  have radix : count (points width pointCount).plan = pointCount := fixedPlan_count width pointCount
  simp only [radix]
  by_cases possible : width ≤ size ∧ pointCount ≠ 0
  · have selected : size - width ∈ List.range (size + 1) := List.mem_range.mpr (by omega)
    rw [flatMap_one (List.range (size + 1)) List.nodup_range (size - width) _ (by
      intro split member different
      have splitBound := List.mem_range.mp member
      have wrong : size - split ≠ width := by omega
      simp [points_groups, wrong])]
    simp [possible, selected, points_groups, show size - (size - width) = width by omega]
    induction liveGroup record (size - width) <;> simp_all
  · have empty : ∀ split ∈ List.range (size + 1),
        liveGroup (points width pointCount) (size - split) = [] := by
      intro split member
      have splitBound := List.mem_range.mp member
      have noPoint : ¬(size - split = width ∧ pointCount ≠ 0) := by omega
      simp [points_groups, noPoint]
    have allEmpty : (List.range (size + 1)).flatMap (fun split =>
        (liveGroup record split).flatMap fun first =>
          (liveGroup (points width pointCount) (size - split)).map fun second =>
            (⟨first.mass * second.mass, Probability.map (fun ranks => pairRank pointCount ranks.1 ranks.2)
              (Probability.product first.weights second.weights)⟩ : Group Nat)) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro split member
      simp [empty split member]
    simpa [possible] using allEmpty

/-- A single valid split does not rescale its internal member weights. -/
theorem singleton_weights (group : Group Nat) (valid : ValidGroup group) : classWeights [group] = group.weights := by
  have countNonzero : (group.count : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr valid.2.1))
  have massNonzero := Rat.ne_of_gt valid.1
  have formula (weight : Rat) : mergeWeight group.count group.mass group.mass group.count weight = weight := by
    simp only [mergeWeight, Rat.div_def]
    calc
      _ = (group.count * (group.count : Rat)⁻¹) * (group.mass * group.mass⁻¹) * weight := by ac_rfl
      _ = weight := by rw [Rat.mul_inv_cancel _ countNonzero, Rat.mul_inv_cancel _ massNonzero]; simp
  simp only [classWeights, List.flatMap_cons, List.flatMap_nil, List.append_nil, memberCount,
    Nat.add_zero, classMass, branches, List.map_cons, List.map_nil, branchWeight, Rat.add_zero]
  have identity : (fun entry : Rat × Nat => (mergeWeight group.count group.mass group.mass group.count entry.1, entry.2)) = id := by
    funext entry; rw [formula]; rfl
  rw [identity, List.map_id]

/-- The derived closure fields equal applyStatic's exact member-weight product, not a new weighting policy. -/
theorem close_weights (width pointCount : Nat) (record : Record) (valid : Valid record) (size : Nat) :
    (close width pointCount record).weights size =
      if width ≤ size then
        Probability.map (fun ranks => pairRank pointCount ranks.1 ranks.2)
          (Probability.product (record.weights (size - width)) (counting (List.range pointCount)))
      else [] := by
  change classWeights (pairGroups record (points width pointCount) size) = _
  rw [close_groups]
  by_cases within : width ≤ size
  · by_cases zero : pointCount = 0
    · simp [within, zero, classWeights, counting, Probability.product, Probability.map]
    · rw [ite_eq_left ⟨within, zero⟩, ite_eq_left within]
      by_cases empty : (record.weights (size - width)).isEmpty = true
      · simp [liveGroup, List.isEmpty_iff.mp empty, classWeights, Probability.product, Probability.map]
      · simp only [liveGroup, empty]
        apply singleton_weights
        have allValid := pairGroups_valid record (points width pointCount) valid (points_valid width pointCount) size
        rw [close_groups] at allValid
        apply allValid
        simp [within, zero, liveGroup, empty]
  · simp [within, classWeights]

/-- The same fixed-width traversal determines the independent class rank lists. -/
theorem close_ranks (width pointCount : Nat) (record : Record) (valid : Valid record) (size : Nat) :
    classRanks (close width pointCount record).plan size =
      if width ≤ size then
        Decoder.applyValues ((classRanks record.plan (size - width)).map
          (fun first second => pairRank pointCount first second)) (List.range pointCount)
      else [] := by
  rw [← (close_valid width pointCount record valid).ranks size, close_weights width pointCount record valid]
  split
  · rw [product_rank_values, valid.ranks]
    simp [counting, List.map_map, Function.comp_def]
  · rfl

/-- CountAtSize uses the original class count times the actual integer point count. -/
theorem close_count_at_size (width pointCount : Nat) (record : Record) (valid : Valid record) (size : Nat) :
    (classRanks (close width pointCount record).plan size).length =
      if width ≤ size then (classRanks record.plan (size - width)).length * pointCount else 0 := by
  rw [close_ranks width pointCount record valid]
  split
  · simp only [Decoder.applyValues, List.length_flatMap, List.map_map, List.length_map, List.length_range, Function.comp_def]
    induction classRanks record.plan (size - width) <;> simp_all [Nat.add_mul, Nat.add_comm]
  · rfl

/-- The whole rank count uses original-major and point-minor product order. -/
theorem close_count (width pointCount : Nat) (record : Record) :
    count (close width pointCount record).plan = count record.plan * pointCount := by
  simp [close, pair, finish, count, points, uniform, fixedPlan_count]


/-- Scaling every live group mass scales their sum by the same factor. -/
theorem map_mass (groups : List (Group Nat)) (factor : Rat) (transform : Group Nat → Group Nat)
    (masses : ∀ group ∈ groups, (transform group).mass = group.mass * factor) :
    classMass (groups.map transform) = classMass groups * factor := by
  induction groups with
  | nil => simp [classMass, branches, branchWeight]
  | cons group rest ih =>
      change (transform group).mass + classMass (rest.map transform) = (group.mass + classMass rest) * factor
      rw [masses group (by simp), ih (fun group member => masses group (by simp [member])), Rat.add_mul]

/-- The source closure multiplies retained size mass by point count and shifts it by width. -/
theorem close_class_mass (width pointCount : Nat) (record : Record) (valid : Valid record) (size : Nat) :
    classMass (pairGroups record (points width pointCount) size) =
      if width ≤ size then massAt record (size - width) * pointCount else 0 := by
  rw [close_groups]
  by_cases within : width ≤ size
  · by_cases zero : pointCount = 0
    · simp [within, zero, classMass, branches, branchWeight]
    · rw [ite_eq_left ⟨within, zero⟩, ite_eq_left within, map_mass _ pointCount _ (by intro group member; rfl),
        liveGroup_mass record valid]
  · simp [within, classMass, branches, branchWeight]

/-- Only the retained table is changed by closedMasses; absent metadata stays absent. -/
theorem close_retained (width pointCount : Nat) (record : Record) (valid : Valid record)
    (masses : Nat → Rat) (retained : record.retained = some masses) (size : Nat) :
    massAt (close width pointCount record) size =
      if width ≤ size then masses (size - width) * pointCount else 0 := by
  have mass := close_class_mass width pointCount record valid size
  simpa [close, pair, finish, points, uniform, massAt, retained] using mass

/-- The source sparse product with one point row is exactly a size shift and mass scaling. -/
theorem sparse_point_product (masses : Sparse.Series Rat) (width pointCount : Nat) :
    Sparse.mulSparse masses [(width, (pointCount : Rat))] = Sparse.shiftScale width (pointCount : Rat) masses := by
  induction masses with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨size, mass⟩ := entry
      simp [Sparse.mulSparse, Sparse.shiftScale, Sparse.addSparse, ih, Nat.add_comm, Rat.mul_comm]

/-- The actual closedMasses implementation has the same lookup as the derived closure field. -/
theorem closedMasses_lookup (width pointCount : Nat) (record : Record) (valid : Valid record)
    (masses : Nat → Rat) (retained : record.retained = some masses) (size : Nat) :
    Sparse.valueAtSize (Sparse.mulSparse (FiniteSizeSeries.series record) [(width, (pointCount : Rat))]) size =
      massAt (close width pointCount record) size := by
  rw [Sparse.valueAtSize_correct _ (Sparse.mulSparse_ordered _ _
    (FiniteSizeSeries.series_ordered record) (by simp [Sparse.Ordered])),
    sparse_point_product, Sparse.coefficient_shiftScale,
    FiniteSizeSeries.series_coefficient record valid, close_retained width pointCount record valid masses retained]
  simp [massAt, retained, Rat.mul_comm]

/-- The decoder position of a closed tuple has the exact original-major, point-minor class rank. -/
theorem close_position (width pointCount : Nat) (record : Record) (valid : Valid record)
    (originalRank : Nat) (part : SizedRank.Position)
    (converted : position record.plan originalRank = some part)
    (pointRank : Nat) (pointInside : pointRank < pointCount) :
    position (close width pointCount record).plan (pairRank pointCount originalRank pointRank) =
      some ⟨part.size + width, pairRank pointCount part.rank pointRank⟩ := by
  apply SourcePlanPartition.position_class_lookup
  have original := SourcePlanPositions.position_replay record.plan originalRank part converted
  have originalInside : part.rank < (classRanks record.plan part.size).length := List.getElem?_eq_some_iff.mp original |>.1
  rw [close_ranks width pointCount record valid]
  simp only [show width ≤ part.size + width by omega, ↓reduceIte, Nat.add_sub_cancel_right]
  rw [Decoder.get_applyValues]
  have bound := pairRank_lt originalInside pointInside
  have split := split_pair (left := part.rank) pointInside
  simp only [splitRank, Prod.mk.injEq] at split
  simp [List.length_map, List.length_range, bound, split.1, split.2, List.getElem?_map,
    original, List.getElem?_range pointInside]

/-- Class lookup inverts this same closed original/point position. -/
theorem close_class_rank (width pointCount : Nat) (record : Record) (valid : Valid record)
    (originalRank : Nat) (part : SizedRank.Position)
    (converted : position record.plan originalRank = some part)
    (pointRank : Nat) (pointInside : pointRank < pointCount) :
    (classRanks (close width pointCount record).plan (part.size + width))[pairRank pointCount part.rank pointRank]? =
      some (pairRank pointCount originalRank pointRank) :=
  SourcePlanPositions.position_replay _ _ _ (close_position width pointCount record valid originalRank part converted pointRank pointInside)


/-- Actual stored retained tables compose through closedMasses without canonical rebuilding. -/
theorem closedMasses_matches (width pointCount : Nat) (record : Record) (valid : Valid record)
    (stored : Sparse.Series Rat) (coherent : FiniteSizeSeries.Matches record stored)
    (masses : Nat → Rat) (retained : record.retained = some masses) :
    FiniteSizeSeries.Matches (close width pointCount record) (Sparse.mulSparse stored [(width, (pointCount : Rat))]) := by
  constructor
  · exact Sparse.mulSparse_ordered _ _ coherent.1 (by simp [Sparse.Ordered])
  · intro size
    rw [FiniteSizeSeries.product_coeff_congr stored [(width, (pointCount : Rat))]
      (FiniteSizeSeries.series record) [(width, (pointCount : Rat))]
      (fun size => (coherent.2 size).trans (FiniteSizeSeries.series_coefficient record valid size).symm)
      (fun size => rfl)]
    rw [← Sparse.valueAtSize_correct _ (Sparse.mulSparse_ordered _ _
      (FiniteSizeSeries.series_ordered record) (by simp [Sparse.Ordered]))]
    exact closedMasses_lookup width pointCount record valid masses retained size

end MicroCFTA.IntegerSizeClosure


