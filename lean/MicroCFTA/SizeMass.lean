import MicroCFTA.Probability
import MicroCFTA.Sized

/-!
# Relative weights within a size class

The Haskell `MassIndex` stores a group's unnormalized mass at each size.
The sampler within that group uses member weights whose sum is its member
count. These two scales are different. This file proves the conversion used
by `frequencyStaticWithMasses` and `pairStaticWithMasses`.

The statements apply to one finite size class. They do not prove construction
of sparse size series, recursive productivity, or the Haskell implementation.
-/

namespace MicroCFTA.SizeMass

open Probability

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- The share of a member inside a class whose relative weights sum to its count. -/
def memberShare (count weight : Rat) : Rat := weight / count

/-- The exact formula in `frequencyStaticWithMasses.weightAt`. -/
def mergeWeight (count mass groupMass groupCount weight : Rat) : Rat :=
  count * groupMass / mass * weight / groupCount

/-- Positive live inputs give a positive relative weight to every member. -/
theorem mergeWeight_positive (count mass groupMass groupCount weight : Rat)
    (hc : 0 < count) (hm : 0 < mass) (hg : 0 < groupMass)
    (hn : 0 < groupCount) (hw : 0 < weight) :
    0 < mergeWeight count mass groupMass groupCount weight := by
  simp only [mergeWeight, Rat.div_def]
  exact Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (Rat.mul_pos hc hg)
    (Rat.inv_pos.mpr hm)) hw) (Rat.inv_pos.mpr hn)

/-- A merge chooses the group by mass and the member by its within-group share. -/
theorem mergeWeight_two_stage (count mass groupMass groupCount weight : Rat) :
    mergeWeight count mass groupMass groupCount weight =
      count * (groupMass / mass) * memberShare groupCount weight := by
  simp only [mergeWeight, memberShare, Rat.div_def]
  ac_rfl

/-- Dividing the result weight by the result count gives the sampler probability. -/
theorem mergeWeight_probability (count mass groupMass groupCount weight : Rat)
    (hn : count ≠ 0) :
    memberShare count (mergeWeight count mass groupMass groupCount weight) =
      (groupMass / mass) * memberShare groupCount weight := by
  rw [mergeWeight_two_stage]
  simp only [memberShare, Rat.div_def]
  calc
    _ = (count * count⁻¹) * (groupMass * mass⁻¹) * (weight * groupCount⁻¹) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hn]; simp

/-- The unnormalized contribution of one member to its group's mass series. -/
def effectiveMass (groupMass groupCount weight : Rat) : Rat :=
  groupMass * memberShare groupCount weight

/-- The merged mass and weights recover the original member's unnormalized mass. -/
theorem mergeWeight_restores_mass (count mass groupMass groupCount weight : Rat)
    (hn : count ≠ 0) (hm : mass ≠ 0) :
    effectiveMass mass count (mergeWeight count mass groupMass groupCount weight) =
      effectiveMass groupMass groupCount weight := by
  rw [effectiveMass, mergeWeight_probability _ _ _ _ _ hn]
  simp only [effectiveMass, memberShare, Rat.div_def]
  calc
    _ = (mass * mass⁻¹) * (groupMass * (weight * groupCount⁻¹)) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hm]; simp

/-- Two merge levels give the same member weight as one direct merge. -/
theorem mergeWeight_associative
    (outerCount outerMass innerCount innerMass groupMass groupCount weight : Rat)
    (hn : innerCount ≠ 0) (hm : innerMass ≠ 0) :
    mergeWeight outerCount outerMass innerMass innerCount
      (mergeWeight innerCount innerMass groupMass groupCount weight) =
    mergeWeight outerCount outerMass groupMass groupCount weight := by
  simp only [mergeWeight, Rat.div_def]
  calc
    _ = (outerCount * groupMass * outerMass⁻¹ * weight * groupCount⁻¹) *
        ((innerCount * innerCount⁻¹) * (innerMass * innerMass⁻¹)) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hn, Rat.mul_inv_cancel _ hm]; simp

/-- Count-weighted selection of a size class cancels its local count scale. -/
theorem bounded_member_probability (classCount totalCount weight : Rat)
    (hc : classCount ≠ 0) :
    classCount / totalCount * memberShare classCount weight = weight / totalCount := by
  simp only [memberShare, Rat.div_def]
  calc
    _ = (classCount * classCount⁻¹) * (weight * totalCount⁻¹) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hc]; simp

/-- The formula in `pairStaticWithMasses.weightAt` for one size split. -/
def pairWeight (count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight : Rat) : Rat :=
  count * (leftMass * rightMass / splitMass) *
    memberShare leftCount leftWeight * memberShare rightCount rightWeight

/-- Pair weights give the split probability times the two conditional member shares. -/
theorem pairWeight_probability
    (count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight : Rat)
    (hn : count ≠ 0) :
    memberShare count
      (pairWeight count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight) =
      (leftMass * rightMass / splitMass) *
        memberShare leftCount leftWeight * memberShare rightCount rightWeight := by
  simp only [pairWeight, memberShare, Rat.div_def]
  calc
    _ = (count * count⁻¹) * ((leftMass * rightMass * splitMass⁻¹) *
        (leftWeight * leftCount⁻¹) * (rightWeight * rightCount⁻¹)) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hn]; simp

/-- Pairing multiplies the effective unnormalized member masses. -/
theorem pairWeight_restores_mass
    (count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight : Rat)
    (hn : count ≠ 0) (hs : splitMass ≠ 0) :
    effectiveMass splitMass count
      (pairWeight count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight) =
      effectiveMass leftMass leftCount leftWeight * effectiveMass rightMass rightCount rightWeight := by
  rw [effectiveMass, pairWeight_probability _ _ _ _ _ _ _ _ hn]
  simp only [effectiveMass, memberShare, Rat.div_def]
  calc
    _ = (splitMass * splitMass⁻¹) *
        (leftMass * (leftWeight * leftCount⁻¹) * (rightMass * (rightWeight * rightCount⁻¹))) := by ac_rfl
    _ = _ := by rw [Rat.mul_inv_cancel _ hs]; simp

/-- One live group within a fixed size class. -/
structure Group (α : Type) where
  mass : Rat
  weights : Distribution α

/-- A structural member count is independent of its weights. -/
def Group.count (group : Group α) : Nat := group.weights.length

/-- The invariant used by `staticSampling` inside each live size class. -/
def ValidGroup (group : Group α) : Prop :=
  0 < group.mass ∧ group.weights ≠ [] ∧
    Nonnegative group.weights ∧ total group.weights = (group.count : Rat)

/-- The structural count of all alternatives of the size class. -/
def memberCount : List (Group α) → Nat
  | [] => 0
  | group :: rest => group.count + memberCount rest

/-- Convert each group's relative weights to its conditional distribution. -/
def branches (groups : List (Group α)) : List (Rat × Distribution α) :=
  groups.map fun group => (group.mass, scale (group.count : Rat)⁻¹ group.weights)

/-- The unnormalized mass of all alternatives of the size class. -/
def classMass (groups : List (Group α)) : Rat := branchWeight (branches groups)

/-- Sample an alternative by mass, then sample within that alternative. -/
def classSampler (groups : List (Group α)) : Distribution α := frequency (branches groups)

/-- Compute the result's relative weights with the Haskell formula. -/
def classWeights (groups : List (Group α)) : Distribution α :=
  groups.flatMap fun group => group.weights.map fun (weight, value) =>
    (mergeWeight (memberCount groups) (classMass groups) group.mass group.count weight, value)

/-- Scaling commutes with concatenation of independent outcome lists. -/
theorem scale_append (factor : Rat) (left right : Distribution α) :
    scale factor (left ++ right) = scale factor left ++ scale factor right := by
  simp [scale]

/-- Expanding a weighted choice gives the same member formulas as `weightAt`. -/
theorem classWeights_eq_scaled_sampler (groups : List (Group α)) :
    classWeights groups = scale (memberCount groups : Rat) (classSampler groups) := by
  have expand (gs : List (Group α)) (factor : Rat) :
      scale factor (mix (branches gs)) =
        gs.flatMap (fun group => group.weights.map fun (weight, value) =>
          (factor * group.mass * (weight / (group.count : Rat)), value)) := by
    induction gs with
    | nil => rfl
    | cons group rest ih =>
        simp only [branches, List.map_cons, mix, List.flatMap_cons]
        rw [scale_append]
        change scale factor (scale group.mass (scale (group.count : Rat)⁻¹ group.weights)) ++
          scale factor (mix (branches rest)) = _
        rw [ih]
        congr 1
        simp [scale, List.map_map, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
  rw [classSampler, frequency, scale_scale]
  rw [expand]
  unfold classWeights classMass
  congr 1
  funext group
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨weight, value⟩
  congr 1
  simp only [mergeWeight, Rat.div_def]
  ac_rfl

/-- A valid group's normalized within-class distribution is a probability. -/
theorem validGroup_probability (group : Group α) (h : ValidGroup group) :
    IsProbability (scale (group.count : Rat)⁻¹ group.weights) := by
  have hn : 0 < group.count := List.length_pos_iff.mpr h.2.1
  have hc : (group.count : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hn)
  constructor
  · exact nonnegative_scale _ _ (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hn))) h.2.2.1
  · rw [total_scale, h.2.2.2, Rat.inv_mul_cancel _ hc]

/-- Nonempty live groups have a positive total structural count. -/
theorem memberCount_positive (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group) : 0 < memberCount groups := by
  cases groups with
  | nil => contradiction
  | cons group rest =>
      have hp : 0 < group.count := List.length_pos_iff.mpr (hv group (by simp)).2.1
      change 0 < group.count + memberCount rest
      omega

/-- Nonempty positive groups give positive total selection mass. -/
theorem classMass_positive (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group) : 0 < classMass groups := by
  have ht : classMass groups = total (groups.map fun group => (group.mass, ())) := by
    clear hn hv
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        simp only [classMass, branches, List.map_cons, branchWeight, total] at *
        exact congrArg (group.mass + ·) ih
  rw [ht]
  apply Sized.total_positive
  · simpa using hn
  · intro entry hm
    obtain ⟨group, hg, rfl⟩ := List.mem_map.mp hm
    exact (hv group hg).1

/-- The two-stage sampler is normalized and has nonnegative masses. -/
theorem classSampler_probability (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group) : IsProbability (classSampler groups) := by
  apply frequency_probability
  · intro entry hm
    obtain ⟨group, hg, rfl⟩ := List.mem_map.mp hm
    exact ⟨Rat.le_of_lt (hv group hg).1, validGroup_probability group (hv group hg)⟩
  · exact classMass_positive groups hn hv

/-- The result weights sum to the result's structural member count. -/
theorem classWeights_total (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group) :
    total (classWeights groups) = (memberCount groups : Rat) := by
  rw [classWeights_eq_scaled_sampler, total_scale, (classSampler_probability groups hn hv).2, Rat.mul_one]

/-- The computed member weights are nonnegative. -/
theorem classWeights_nonnegative (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group) : Nonnegative (classWeights groups) := by
  rw [classWeights_eq_scaled_sampler]
  exact nonnegative_scale _ _ Rat.natCast_nonneg (classSampler_probability groups hn hv).1

/-- No positive input rank loses all of its probability during a valid merge. -/
theorem classWeights_positive (groups : List (Group α)) (hn : groups ≠ [])
    (hv : ∀ group ∈ groups, ValidGroup group)
    (hp : ∀ group ∈ groups, ∀ entry ∈ group.weights, 0 < entry.1) :
    ∀ entry ∈ classWeights groups, 0 < entry.1 := by
  intro entry he
  obtain ⟨group, hg, he⟩ := List.mem_flatMap.mp he
  obtain ⟨⟨weight, value⟩, hw, rfl⟩ := List.mem_map.mp he
  exact mergeWeight_positive _ _ _ _ _
    (Rat.natCast_pos.mpr (memberCount_positive groups hn hv))
    (classMass_positive groups hn hv) (hv group hg).1
    (Rat.natCast_pos.mpr (List.length_pos_iff.mpr (hv group hg).2.1)) (hp group hg _ hw)

/-- Build one conditional bucket from raw member masses.
Its retained mass is the sum of the raw masses. Its internal weights sum to
its own structural count. -/
def bucket (members : Distribution α) : Group α :=
  ⟨total members, scale (members.length : Rat) (normalize members)⟩

/-- Bucket normalization preserves one replay position per input member. -/
theorem bucket_count (members : Distribution α) : (bucket members).count = members.length := by
  simp [bucket, Group.count, scale, normalize]

/-- Positive nonempty input gives a valid conditional bucket. -/
theorem bucket_valid (members : Distribution α) (hn : members ≠ [])
    (hp : ∀ entry ∈ members, 0 < entry.1) : ValidGroup (bucket members) := by
  have hm : 0 < total members := Sized.total_positive members hn hp
  have hp' : IsProbability (normalize members) := normalize_probability members
    (fun entry he => Rat.le_of_lt (hp entry he)) hm
  refine ⟨hm, ?_, ?_, ?_⟩
  · simpa [bucket, scale, normalize] using hn
  · exact nonnegative_scale _ _ Rat.natCast_nonneg hp'.1
  · change total (scale (members.length : Rat) (normalize members)) = ((bucket members).count : Rat)
    rw [total_scale, hp'.2, Rat.mul_one, bucket_count]

/-- The local count scale cancels when the bucket is sampled. -/
theorem bucket_conditional (members : Distribution α) (hn : members ≠ []) :
    scale ((bucket members).count : Rat)⁻¹ (bucket members).weights = normalize members := by
  have hc : (members.length : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr hn))
  rw [bucket_count]
  change scale (members.length : Rat)⁻¹ (scale (members.length : Rat) (normalize members)) = _
  rw [scale_scale, Rat.inv_mul_cancel _ hc, scale_one]

/-- Partition a source class by its actual observation keys and retain its masses. -/
def splitClass [DecidableEq Key] (key : Rat × α → Key) (members : Distribution α) : List (Group α) :=
  (Sized.groups key members).map bucket

/-- The concrete partition produces valid buckets when every input mass is positive. -/
theorem splitClass_valid [DecidableEq Key] (key : Rat × α → Key) (members : Distribution α)
    (hp : ∀ entry ∈ members, 0 < entry.1) :
    ∀ group ∈ splitClass key members, ValidGroup group := by
  intro group hg
  obtain ⟨part, hm, rfl⟩ := List.mem_map.mp hg
  obtain ⟨first, rest, heq, _⟩ := Sized.groups_constant key members part hm
  apply bucket_valid
  · simp [heq]
  · intro entry he
    exact hp entry ((Sized.groups_perm key members).mem_iff.mp (List.mem_flatten.mpr ⟨part, hm, he⟩))

/-- Splitting stores exactly the conditional distributions and their original masses. -/
theorem splitClass_branches [DecidableEq Key] (key : Rat × α → Key) (members : Distribution α) :
    branches (splitClass key members) = conditionalBuckets (Sized.groups key members) := by
  simp only [branches, splitClass, List.map_map, conditionalBuckets]
  apply List.map_congr_left
  intro part hm
  obtain ⟨first, rest, heq, _⟩ := Sized.groups_constant key members part hm
  simp only [Function.comp_def, bucket_conditional part (by simp [heq])]
  rfl

/-- Splitting by a finite observation and then merging preserves each output probability. -/
theorem split_merge_probability [DecidableEq Key] (key : Rat × α → Key)
    (members : Distribution α) (hp : ∀ entry ∈ members, 0 < entry.1) (event : α → Bool) :
    eventMass event (classSampler (splitClass key members)) = eventMass event (normalize members) := by
  rw [classSampler, splitClass_branches]
  exact Sized.partition_conditional_probability key members hp event

/-- The structural count of normalized buckets is the number of source members. -/
theorem memberCount_buckets (parts : List (Distribution α)) :
    memberCount (parts.map bucket) = parts.flatten.length := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
      simp only [List.map_cons, memberCount, bucket_count, List.flatten_cons, List.length_append, ih]

/-- The concrete split preserves every replay position, including repeated outputs. -/
theorem splitClass_count [DecidableEq Key] (key : Rat × α → Key) (members : Distribution α) :
    memberCount (splitClass key members) = members.length := by
  rw [splitClass, memberCount_buckets, (Sized.groups_perm key members).length_eq]

/-- Splitting and merging preserves the source's count-scaled event weights. -/
theorem split_merge_weight [DecidableEq Key] (key : Rat × α → Key)
    (members : Distribution α) (hp : ∀ entry ∈ members, 0 < entry.1)
    (hn : members ≠ []) (ht : total members = (members.length : Rat)) (event : α → Bool) :
    eventMass event (classWeights (splitClass key members)) = eventMass event members := by
  rw [classWeights_eq_scaled_sampler, eventMass_scale, splitClass_count,
    split_merge_probability key members hp event, normalize, eventMass_scale, ht]
  have hc : (members.length : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr hn))
  rw [← Rat.mul_assoc, Rat.mul_inv_cancel _ hc, Rat.one_mul]

/-- Applying a size predicate before splitting preserves the exact conditional distribution. -/
theorem split_merge_at_size [DecidableEq Key] (key : Rat × α → Key)
    (members : Distribution α) (hp : ∀ entry ∈ members, 0 < entry.1)
    (sizeOf : α → Nat) (wantedSize : Nat) (event : α → Bool) :
    eventMass event (classSampler (splitClass key
      (restrict (fun value => sizeOf value == wantedSize) members))) =
    eventMass event (condition (fun value => sizeOf value == wantedSize) members) := by
  apply split_merge_probability
  intro entry he
  exact hp entry (List.mem_filter.mp he).1

/-- An applicative product retains one position for every pair of component ranks. -/
theorem product_length (left : Distribution α) (right : Distribution β) :
    (product left right).length = left.length * right.length := by
  induction left with
  | nil => simp [product]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      change ((right.map fun (entry : Rat × β) => (mass * entry.1, (value, entry.2))) ++ product rest right).length = _
      rw [List.length_append, List.length_map, ih]
      simp [Nat.add_mul, Nat.add_comm]

/-- A product group multiplies both the retained masses and the internal member weights. -/
def pairGroup (left : Group α) (right : Group β) : Group (α × β) :=
  ⟨left.mass * right.mass, product left.weights right.weights⟩

/-- Product cardinalities use the same mixed-radix count as their rank decoder. -/
theorem pairGroup_count (left : Group α) (right : Group β) :
    (pairGroup left right).count = left.count * right.count := by
  exact product_length left.weights right.weights

/-- Positive valid component groups produce a positive valid product group. -/
theorem pairGroup_valid (left : Group α) (right : Group β)
    (hl : ValidGroup left) (hr : ValidGroup right) : ValidGroup (pairGroup left right) := by
  refine ⟨Rat.mul_pos hl.1 hr.1, ?_, ?_, ?_⟩
  · apply List.length_pos_iff.mp
    change 0 < (product left.weights right.weights).length
    rw [product_length]
    exact Nat.mul_pos (List.length_pos_iff.mpr hl.2.1) (List.length_pos_iff.mpr hr.2.1)
  · intro entry he
    obtain ⟨⟨lm, lv⟩, hlm, her⟩ := List.mem_flatMap.mp he
    obtain ⟨⟨rm, rv⟩, hrm, rfl⟩ := List.mem_map.mp her
    exact Rat.mul_nonneg (hl.2.2.1 _ hlm) (hr.2.2.1 _ hrm)
  · change total (product left.weights right.weights) = ((pairGroup left right).count : Rat)
    rw [total_product, hl.2.2.2, hr.2.2.2, pairGroup_count, Rat.natCast_mul]

/-- The pair `weightAt` formula is exactly the merge formula for a product group. -/
theorem pairWeight_eq_mergeWeight
    (count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight : Rat) :
    pairWeight count splitMass leftMass rightMass leftCount rightCount leftWeight rightWeight =
      mergeWeight count splitMass (leftMass * rightMass) (leftCount * rightCount) (leftWeight * rightWeight) := by
  simp only [pairWeight, mergeWeight, memberShare, Rat.div_def, Rat.inv_mul_rev]
  ac_rfl

/-- Choosing positive product groups by split mass yields a probability distribution. -/
theorem split_product_probability (splits : List (Group α × Group β))
    (hn : splits ≠ []) (hv : ∀ pair ∈ splits, ValidGroup pair.1 ∧ ValidGroup pair.2) :
    IsProbability (classSampler (splits.map fun pair => pairGroup pair.1 pair.2)) := by
  apply classSampler_probability
  · simpa using hn
  · intro group hg
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hg
    exact pairGroup_valid pair.1 pair.2 (hv pair hp).1 (hv pair hp).2

/-- Result weights of positive size splits sum to their structural product count. -/
theorem split_product_weights_total (splits : List (Group α × Group β))
    (hn : splits ≠ []) (hv : ∀ pair ∈ splits, ValidGroup pair.1 ∧ ValidGroup pair.2) :
    total (classWeights (splits.map fun pair => pairGroup pair.1 pair.2)) =
      (memberCount (splits.map fun pair => pairGroup pair.1 pair.2) : Rat) := by
  apply classWeights_total
  · simpa using hn
  · intro group hg
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hg
    exact pairGroup_valid pair.1 pair.2 (hv pair hp).1 (hv pair hp).2

/-- Positive atomic bucket masses cannot be replaced by member counts during a pair merge. -/
theorem atomic_pair_count_fallback_changes_probability :
    memberShare 2 (mergeWeight 2 10 9 1 1) = 9 / 10 ∧
      memberShare 2 (mergeWeight 2 2 1 1 1) = 1 / 2 ∧
      (9 / 10 : Rat) ≠ 1 / 2 := by decide +kernel

end MicroCFTA.SizeMass
