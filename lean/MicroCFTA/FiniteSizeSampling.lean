import MicroCFTA.FiniteSizeFields

/-!
# Finite size sampler and mass lookup correspondence

The source weight callback first finds the member's size. Class lookup then
uses the same position. Product masses include the zero-size split.
-/
namespace MicroCFTA.FiniteSizeSampling
open Probability SourcePlanPositions SizeMass FiniteSizeFields

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- Read a source relative weight at the actual original member rank. -/
def weightAt (record : Record) (rank : Nat) : Option Rat := do
  let part ← position record.plan rank
  let entry ← (record.weights part.size)[part.rank]?
  pure entry.1

/-- A source class lookup supplies both the original rank and its relative weight. -/
theorem class_lookup (record : Record) (valid : Valid record) (part : SizedRank.Position) (rank : Nat)
    (converted : position record.plan rank = some part) :
    ∃ weight, (record.weights part.size)[part.rank]? = some (weight, rank) ∧
      weightAt record rank = some weight ∧ 0 < weight := by
  have ranked := (position_weights record valid part rank).mp converted
  rw [List.getElem?_map] at ranked
  obtain ⟨entry, found, same⟩ := Option.map_eq_some_iff.mp ranked
  have second : entry.2 = rank := same
  obtain ⟨weight, original⟩ := entry
  dsimp only at second
  subst original
  exact ⟨weight, found, by simp [weightAt, converted, found],
    valid.positive part.size (weight, rank) (List.mem_of_getElem? found)⟩

/-- The class weight callback has exactly the same successful interval as the decoder plan. -/
theorem weightAt_exists (record : Record) (valid : Valid record) (rank : Nat) :
    (∃ weight, weightAt record rank = some weight) ↔ rank < count record.plan := by
  constructor
  · rintro ⟨weight, found⟩
    cases converted : position record.plan rank with
    | none => simp [weightAt, converted] at found
    | some part => exact (position_exists_iff record.plan rank).mp ⟨part, converted⟩
  · intro inside
    obtain ⟨part, converted⟩ := position_complete record.plan rank inside
    obtain ⟨weight, _, found, _⟩ := class_lookup record valid part rank converted
    exact ⟨weight, found⟩

/-- The source converts its count-scale weights into conditional member probabilities. -/
def sample (record : Record) (size : Nat) : Distribution Nat :=
  scale ((classRanks record.plan size).length : Rat)⁻¹ (record.weights size)

/-- Every live class has a normalized positive sampler derived from its field constructor. -/
theorem sample_probability (record : Record) (valid : Valid record) (size : Nat)
    (nonempty : classRanks record.plan size ≠ []) : IsProbability (sample record size) := by
  have membersNonempty : record.weights size ≠ [] := fun empty => nonempty ((weights_empty record valid size).mp empty)
  have result := validGroup_probability (classGroup record size) (class_valid record valid size membersNonempty)
  have lengths := congrArg List.length (valid.ranks size)
  have countEq : (record.weights size).length = (classRanks record.plan size).length := by simpa using lengths
  simpa [sample, classGroup, Group.count, countEq] using result

/-- No rank appears twice in the source class sampler. -/
theorem sample_ranks (record : Record) (valid : Valid record) (size : Nat) :
    (sample record size).map Prod.snd = classRanks record.plan size ∧
      ((sample record size).map Prod.snd).Nodup := by
  have same : (sample record size).map Prod.snd = classRanks record.plan size := by
    simpa [sample, scale, List.map_map, Function.comp_def] using valid.ranks size
  exact ⟨same, by rw [same]; exact SourcePlanPartition.class_nodup record.plan size⟩

/-- The local sampler selects exactly the ranks listed by the independent class partition. -/
theorem sample_support (record : Record) (valid : Valid record) (size rank : Nat) :
    (∃ mass, (mass, rank) ∈ sample record size ∧ 0 < mass) ↔ rank ∈ classRanks record.plan size := by
  constructor
  · rintro ⟨mass, present, _⟩
    rw [← (sample_ranks record valid size).1]
    exact List.mem_map.mpr ⟨(mass, rank), present, rfl⟩
  · intro member
    have nonempty : classRanks record.plan size ≠ [] := List.ne_nil_of_mem member
    rw [← valid.ranks size] at member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    refine ⟨((classRanks record.plan size).length : Rat)⁻¹ * entry.1, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨entry, present, by simp [same]⟩
    · exact Rat.mul_pos (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (List.length_pos_iff.mpr nonempty)))
        (valid.positive size entry present)

/-- The constructed weighted split sampler is the source classSampler. -/
theorem finish_sample (plan : Plan) (groups : Nat → List (Group Nat)) (retain : Bool)
    (ranks : ∀ size, (groups size).flatMap (fun group => group.weights.map Prod.snd) = classRanks plan size)
    (valid : ∀ size group, group ∈ groups size → ValidGroup group)
    (size : Nat) (nonempty : groups size ≠ []) :
    sample (finish plan groups retain) size = classSampler (groups size) := by
  have counts : memberCount (groups size) = (classRanks plan size).length := by rw [← ranks_count, ranks]
  change scale ((classRanks plan size).length : Rat)⁻¹ (classWeights (groups size)) = _
  rw [classWeights_eq_scaled_sampler, scale_scale, ← counts,
    Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr (memberCount_positive _ nonempty (valid size)))), scale_one]

theorem classMass_append (left right : List (Group Nat)) :
    classMass (left ++ right) = classMass left + classMass right := by
  induction left with
  | nil => simp [classMass, branches, branchWeight, Rat.zero_add]
  | cons first rest ih =>
      change first.mass + classMass (rest ++ right) = (first.mass + classMass rest) + classMass right
      rw [ih, Rat.add_assoc]

theorem classMass_map (f : Group Nat → Group Nat) (groups : List (Group Nat))
    (mass : ∀ group ∈ groups, (f group).mass = group.mass) : classMass (groups.map f) = classMass groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change (f group).mass + classMass (rest.map f) = group.mass + classMass rest
      rw [mass group (by simp), ih (fun group member => mass group (by simp [member]))]

/-- Source sumMassIndexes adds unnormalized class masses without outer branch weights. -/
theorem choiceGroups_mass (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (offset size : Nat) : classMass (choiceGroups offset records size) =
      (records.map (fun record => massAt record size)).sum := by
  induction records generalizing offset with
  | nil => rfl
  | cons record rest ih =>
      rw [choiceGroups, classMass_append,
        classMass_map (offsetGroup offset) _ (by intro group member; rfl),
        liveGroup_mass record (valid record (by simp)), ih (fun record member => valid record (by simp [member]))]
      rfl

/-- The general product helper multiplies the masses of both live classes. -/
theorem cartesian_mass (left right : List (Group Nat)) (radix : Nat) :
    classMass (left.flatMap (fun first => right.map (fun second =>
      ⟨first.mass * second.mass, Probability.map (fun ranks => pairRank radix ranks.1 ranks.2)
        (Probability.product first.weights second.weights)⟩))) = classMass left * classMass right := by
  induction left with
  | nil => simp [classMass, branches, branchWeight]
  | cons first rest ih =>
      simp only [List.flatMap_cons, classMass_append, ih]
      have inner : classMass (right.map (fun second =>
          ⟨first.mass * second.mass, Probability.map (fun ranks => pairRank radix ranks.1 ranks.2)
            (Probability.product first.weights second.weights)⟩)) = first.mass * classMass right := by
        clear ih
        induction right with
        | nil => simp [classMass, branches, branchWeight]
        | cons second rest ih =>
            change first.mass * second.mass + classMass _ = first.mass * (second.mass + classMass rest)
            rw [ih, Rat.mul_add]
      rw [inner]
      change first.mass * classMass right + classMass rest * classMass right = (first.mass + classMass rest) * classMass right
      rw [Rat.add_mul]

/-- pairMassIndex and pairStaticWithMasses use the same complete nonnegative size splits. -/
theorem pairGroups_mass (left right : Record) (leftValid : Valid left) (rightValid : Valid right) (size : Nat) :
    classMass (pairGroups left right size) =
      ((List.range (size + 1)).map (fun split => massAt left split * massAt right (size - split))).sum := by
  have expand : ∀ sizes : List Nat, classMass (sizes.flatMap (fun split =>
      (liveGroup left split).flatMap (fun first => (liveGroup right (size - split)).map (fun second =>
        ⟨first.mass * second.mass, Probability.map (fun ranks => pairRank (count right.plan) ranks.1 ranks.2)
          (Probability.product first.weights second.weights)⟩)))) =
      (sizes.map (fun split => massAt left split * massAt right (size - split))).sum := by
    intro sizes
    induction sizes with
    | nil => rfl
    | cons split rest ih =>
        rw [List.flatMap_cons, classMass_append, cartesian_mass,
          liveGroup_mass left leftValid, liveGroup_mass right rightValid, ih]
        rfl
  exact expand _

/-- The retained source pair mass field equals the mass used to choose its size split. -/
theorem pair_retained_mass (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (retained : (left.retained.isSome || right.retained.isSome) = true) (size : Nat) :
    massAt (sourcePair left right) size =
      ((List.range (size + 1)).map (fun split => massAt left split * massAt right (size - split))).sum := by
  change (match (if left.retained.isSome || right.retained.isSome then some (fun size => classMass (pairGroups left right size)) else none) with
    | none => ((classRanks (pairPlan left.plan right.plan) size).length : Rat)
    | some masses => masses size) = _
  rw [retained]
  exact pairGroups_mass left right leftValid rightValid size

/-- The retained source choice mass field is the sum of child class masses. -/
theorem choice_retained_mass (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (retained : records.any (fun record => record.retained.isSome) = true) (size : Nat) :
    massAt (choice records) size = (records.map (fun record => massAt record size)).sum := by
  simp only [choice, finish, massAt, retained, ↓reduceIte]
  exact choiceGroups_mass records valid 0 size


/-- An absent retained table gives every live group its exact member count as mass. -/
theorem live_count_mass (record : Record) (valid : Valid record) (absent : record.retained = none)
    (size : Nat) (group : Group Nat) (member : group ∈ liveGroup record size) : group.mass = (group.count : Rat) := by
  unfold liveGroup at member
  split at member
  · cases member
  · have same : group = classGroup record size := by simpa using member
    subst group
    have length := congrArg List.length (valid.ranks size)
    simp only [List.length_map] at length
    simp [classGroup, massAt, absent, Group.count, length]

/-- The ordinary product path keeps the product of child relative weights at each size split. -/
theorem pair_without_retained (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (leftAbsent : left.retained = none) (rightAbsent : right.retained = none) (size : Nat) :
    (pair left right).weights size = (List.range (size + 1)).flatMap (fun split =>
      Probability.map (fun ranks => pairRank (count right.plan) ranks.1 ranks.2)
        (Probability.product (left.weights split) (right.weights (size - split)))) := by
  change classWeights (pairGroups left right size) = _
  rw [count_mass_classes _ (pairGroups_valid left right leftValid rightValid size) (by
    intro group member
    obtain ⟨split, _, first, firstMember, second, secondMember, rfl⟩ := by
      simpa only [pairGroups, List.mem_flatMap, List.mem_map] using member
    have leftCount := live_count_mass left leftValid leftAbsent split first firstMember
    have rightCount := live_count_mass right rightValid rightAbsent (size - split) second secondMember
    simp only [leftCount, rightCount, Group.count, Probability.map, List.length_map, SizeMass.product_length, Rat.natCast_mul])]
  simp only [pairGroups, List.flatMap_assoc, List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro split member
  unfold liveGroup
  split <;> split <;> simp_all [classGroup, Probability.product, Probability.map]

/-- The source ordinary frequency callback leaves each child relative weight unchanged. -/
def ordinaryChoiceWeights (offset : Nat) : List Record → Nat → Distribution Nat
  | [], _ => []
  | record :: rest, size => Probability.map (offset + ·) (record.weights size) ++
      ordinaryChoiceWeights (offset + count record.plan) rest size

theorem choice_groups_weights (records : List Record) (offset size : Nat) :
    (choiceGroups offset records size).flatMap Group.weights = ordinaryChoiceWeights offset records size := by
  induction records generalizing offset with
  | nil => rfl
  | cons record rest ih =>
      simp only [choiceGroups, List.flatMap_append, List.flatMap_map, ordinaryChoiceWeights, ih]
      congr 1
      unfold liveGroup
      split <;> simp_all [offsetGroup, classGroup, Probability.map]

/-- Count fallback agrees with the actual ordinary frequency path for any number of alternatives. -/
theorem choice_without_retained (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (absent : ∀ record ∈ records, record.retained = none) (size : Nat) :
    (choice records).weights size = ordinaryChoiceWeights 0 records size := by
  have groupsCount : ∀ (records : List Record), (∀ record ∈ records, Valid record) →
      (∀ record ∈ records, record.retained = none) → ∀ offset group,
        group ∈ choiceGroups offset records size → group.mass = (group.count : Rat) := by
    intro records
    induction records with
    | nil => intro valid absent offset group member; cases member
    | cons record rest ih =>
        intro valid absent offset group member
        rcases List.mem_append.mp member with front | tail
        · obtain ⟨original, present, rfl⟩ := List.mem_map.mp front
          have same := live_count_mass record (valid record (by simp)) (absent record (by simp)) size original present
          simpa [offsetGroup, Group.count, Probability.map] using same
        · exact ih (fun record member => valid record (by simp [member]))
            (fun record member => absent record (by simp [member])) _ group tail
  change classWeights (choiceGroups 0 records size) = _
  rw [count_mass_classes _ (choiceGroups_valid records valid 0 size) (groupsCount records valid absent 0), choice_groups_weights]


/-- Any listed class member has that same relative weight at its original replay rank. -/
theorem weightAt_member (record : Record) (valid : Valid record) (size rank : Nat) (weight : Rat)
    (member : (weight, rank) ∈ record.weights size) : weightAt record rank = some weight := by
  obtain ⟨classRank, found⟩ := List.getElem?_of_mem member
  have converted : position record.plan rank = some ⟨size, classRank⟩ := by
    apply (position_weights record valid _ rank).mpr
    rw [List.getElem?_map, found]
    rfl
  simp [weightAt, converted, found]

/-- The original rank callback returns precisely the member listed by its computed size class. -/
theorem weightAt_in_class (record : Record) (valid : Valid record) (rank : Nat) (part : SizedRank.Position)
    (converted : position record.plan rank = some part) (weight : Rat) (found : weightAt record rank = some weight) :
    (weight, rank) ∈ record.weights part.size := by
  obtain ⟨actual, selected, replay, _⟩ := class_lookup record valid part rank converted
  have same := Option.some.inj (replay.symm.trans found)
  subst actual
  exact List.mem_of_getElem? selected

/-- pairStaticWithMasses.weightAt follows the actual child ranks, sizes, and per-size mass fields. -/
theorem pair_weightAt (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (leftRank rightRank : Nat) (leftPart rightPart : SizedRank.Position)
    (leftPosition : position left.plan leftRank = some leftPart)
    (rightPosition : position right.plan rightRank = some rightPart)
    (leftWeight rightWeight : Rat)
    (leftFound : weightAt left leftRank = some leftWeight) (rightFound : weightAt right rightRank = some rightWeight) :
    let size := leftPart.size + rightPart.size
    weightAt (sourcePair left right) (pairRank (count right.plan) leftRank rightRank) =
      some (pairWeight (classRanks (pairPlan left.plan right.plan) size).length
        (classMass (pairGroups left right size)) (massAt left leftPart.size) (massAt right rightPart.size)
        (classRanks left.plan leftPart.size).length (classRanks right.plan rightPart.size).length
        leftWeight rightWeight) := by
  dsimp only
  have leftMember := weightAt_in_class left leftValid leftRank leftPart leftPosition leftWeight leftFound
  have rightMember := weightAt_in_class right rightValid rightRank rightPart rightPosition rightWeight rightFound
  let joined : Group Nat :=
    ⟨massAt left leftPart.size * massAt right rightPart.size,
      Probability.map (fun ranks => pairRank (count right.plan) ranks.1 ranks.2)
        (Probability.product (left.weights leftPart.size) (right.weights rightPart.size))⟩
  have groupMember : joined ∈ pairGroups left right (leftPart.size + rightPart.size) := by
    apply List.mem_flatMap.mpr
    refine ⟨leftPart.size, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨classGroup left leftPart.size, ?_, ?_⟩
    · simp [liveGroup, List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem leftMember)]
    · apply List.mem_map.mpr
      refine ⟨classGroup right rightPart.size, ?_, rfl⟩
      simp [liveGroup, List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem rightMember)]
  have productMember : (leftWeight * rightWeight, pairRank (count right.plan) leftRank rightRank) ∈ joined.weights := by
    apply List.mem_map.mpr
    refine ⟨(leftWeight * rightWeight, (leftRank, rightRank)), ?_, rfl⟩
    apply List.mem_flatMap.mpr
    exact ⟨(leftWeight, leftRank), leftMember,
      List.mem_map.mpr ⟨(rightWeight, rightRank), rightMember, rfl⟩⟩
  have resultCount : memberCount (pairGroups left right (leftPart.size + rightPart.size)) =
      (classRanks (pairPlan left.plan right.plan) (leftPart.size + rightPart.size)).length := by
    rw [← ranks_count, pairGroups_ranks left right leftValid rightValid, pairPlan_classes]
  have childCount : joined.count = (classRanks left.plan leftPart.size).length * (classRanks right.plan rightPart.size).length := by
    have leftLength := congrArg List.length (leftValid.ranks leftPart.size)
    have rightLength := congrArg List.length (rightValid.ranks rightPart.size)
    simp only [List.length_map] at leftLength rightLength
    simp [joined, Group.count, Probability.map, product_length, leftLength, rightLength]
  apply weightAt_member _ (sourcePair_valid left right leftValid rightValid) (leftPart.size + rightPart.size)
  change (_, _) ∈ classWeights (pairGroups left right (leftPart.size + rightPart.size))
  apply List.mem_flatMap.mpr
  refine ⟨joined, groupMember, List.mem_map.mpr ⟨_, productMember, ?_⟩⟩
  simp only [Prod.mk.injEq, and_true, resultCount, childCount, pairWeight_eq_mergeWeight, Rat.natCast_mul]
  rfl


/-- Every source alternative retains its class group under the exact global prefix offset. -/
theorem choice_group_member (before after : List Record) (record : Record) (start size : Nat)
    (group : Group Nat) (member : group ∈ liveGroup record size) :
    offsetGroup (start + (before.map (fun record => count record.plan)).sum) group ∈
      choiceGroups start (before ++ record :: after) size := by
  induction before generalizing start with
  | nil =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨group, member, by simp⟩
  | cons first before ih =>
      apply List.mem_append_right
      simpa [Nat.add_assoc] using ih (start + count first.plan)

/-- frequencyStaticWithMasses.weightAt uses the same branch offset as the global term decoder. -/
theorem choice_weightAt (before after : List Record) (record : Record)
    (valid : ∀ child ∈ before ++ record :: after, Valid child)
    (rank : Nat) (part : SizedRank.Position) (converted : position record.plan rank = some part)
    (weight : Rat) (found : weightAt record rank = some weight) :
    let records := before ++ record :: after
    let offset := (before.map (fun child => count child.plan)).sum
    weightAt (choice records) (offset + rank) = some
      (mergeWeight (classRanks (choicePlan records) part.size).length
        (classMass (choiceGroups 0 records part.size)) (massAt record part.size)
        (classRanks record.plan part.size).length weight) := by
  dsimp only
  have current := valid record (by simp)
  have member := weightAt_in_class record current rank part converted weight found
  have live : classGroup record part.size ∈ liveGroup record part.size := by
    simp [liveGroup, List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem member)]
  have groupMember := choice_group_member before after record 0 part.size (classGroup record part.size) live
  simp only [Nat.zero_add] at groupMember
  have shifted : (weight, (before.map (fun child => count child.plan)).sum + rank) ∈
      (offsetGroup (before.map (fun child => count child.plan)).sum (classGroup record part.size)).weights :=
    List.mem_map.mpr ⟨(weight, rank), member, rfl⟩
  have resultCount : memberCount (choiceGroups 0 (before ++ record :: after) part.size) =
      (classRanks (choicePlan (before ++ record :: after)) part.size).length := by
    rw [← ranks_count, choiceGroups_ranks _ valid]
    simp
  have childCount := congrArg List.length (current.ranks part.size)
  simp only [List.length_map] at childCount
  apply weightAt_member _ (choice_valid _ valid) part.size
  change (_, _) ∈ classWeights (choiceGroups 0 (before ++ record :: after) part.size)
  apply List.mem_flatMap.mpr
  refine ⟨_, groupMember, List.mem_map.mpr ⟨_, shifted, ?_⟩⟩
  simp [offsetGroup, classGroup, Group.count, Probability.map, childCount, resultCount]


/-- The actual positive-mass backend chooser implements the derived class mixture. -/
theorem mass_sampler (groups : List (Group Nat)) (nonempty : groups ≠ [])
    (valid : ∀ group ∈ groups, ValidGroup group) :
    Sampler.chooseMassWeighted (branches groups) = some (classSampler groups) := by
  have live : Sampler.liveMasses (branches groups) = branches groups := by
    apply List.filter_eq_self.mpr
    intro entry member
    obtain ⟨group, present, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (valid group present).1
  have someLive : Sampler.liveMasses (branches groups) ≠ [] := by
    rw [live]
    simpa [branches] using nonempty
  simpa [live, classSampler] using Sampler.chooseMassWeighted_correct (branches groups) someLive

/-- The concrete product-mass chooser and the source relative-weight callback define the same class probability. -/
theorem pair_sampler (left right : Record) (leftValid : Valid left) (rightValid : Valid right) (size : Nat)
    (nonempty : classRanks (pairPlan left.plan right.plan) size ≠ []) :
    Sampler.chooseMassWeighted (branches (pairGroups left right size)) = some (sample (sourcePair left right) size) := by
  have groupsNonempty : pairGroups left right size ≠ [] := by
    intro empty
    have ranks := pairGroups_ranks left right leftValid rightValid size
    rw [empty] at ranks
    exact nonempty (by simpa [pairPlan_classes] using ranks.symm)
  rw [mass_sampler _ groupsNonempty (pairGroups_valid left right leftValid rightValid size)]
  congr 1
  have sampler := finish_sample (.ap left.plan right.plan) (pairGroups left right)
    (left.retained.isSome || right.retained.isSome) (pairGroups_ranks left right leftValid rightValid)
    (pairGroups_valid left right leftValid rightValid) size groupsNonempty
  change _ = sample (sourcePair left right) size
  rw [← sampler]
  simp only [sample, sourcePair, pairPlan_classes]
  rfl

/-- The concrete choice-mass chooser and its weight callback also agree for every finite observation merge. -/
theorem choice_sampler (records : List Record) (valid : ∀ record ∈ records, Valid record) (size : Nat)
    (nonempty : classRanks (choicePlan records) size ≠ []) :
    Sampler.chooseMassWeighted (branches (choiceGroups 0 records size)) = some (sample (choice records) size) := by
  have ranks (size : Nat) : (choiceGroups 0 records size).flatMap (fun group => group.weights.map Prod.snd) =
      classRanks (choicePlan records) size := by simpa using choiceGroups_ranks records valid 0 size
  have groupsNonempty : choiceGroups 0 records size ≠ [] := by
    intro empty
    have same := ranks size
    rw [empty] at same
    exact nonempty same.symm
  rw [mass_sampler _ groupsNonempty (choiceGroups_valid records valid 0 size)]
  congr 1
  exact (finish_sample (choicePlan records) (choiceGroups 0 records)
    (records.any (fun record => record.retained.isSome)) ranks (choiceGroups_valid records valid 0) size groupsNonempty).symm

end MicroCFTA.FiniteSizeSampling




