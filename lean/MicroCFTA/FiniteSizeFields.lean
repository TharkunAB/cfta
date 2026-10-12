import MicroCFTA.FinalObservationMass
import MicroCFTA.SourcePlanPartition
import MicroCFTA.SizeTransport

/-!
# Finite size fields built from source constructors

Member weights inside a size class sum to its count. A retained bucket mass
uses a different scale. Both fields are constructed with the class rank lists.
-/
namespace MicroCFTA.FiniteSizeFields
open Probability SourcePlanPositions SizeMass

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- The finite fields read by staticSampling and bucketMassIndex. -/
structure Record where
  plan : Plan
  weights : Nat → Distribution Nat
  retained : Option (Nat → Rat)

/-- Missing retained masses use source member counts. -/
def massAt (record : Record) (size : Nat) : Rat :=
  match record.retained with
  | none => ((classRanks record.plan size).length : Rat)
  | some masses => masses size

/-- Class ranks, relative weights, and optional retained masses agree. -/
structure Valid (record : Record) : Prop where
  ranks : ∀ size, (record.weights size).map Prod.snd = classRanks record.plan size
  positive : ∀ size entry, entry ∈ record.weights size → 0 < entry.1
  total : ∀ size, Probability.total (record.weights size) = ((classRanks record.plan size).length : Rat)
  mass : ∀ size, if (classRanks record.plan size).isEmpty then massAt record size = 0 else 0 < massAt record size

/-- A source with no inherited weights samples every size class uniformly. -/
def uniform (plan : Plan) : Record := ⟨plan, fun size => counting (classRanks plan size), none⟩

/-- The ordinary source fallback derives every class weight from its actual rank list. -/
theorem uniform_valid (plan : Plan) : Valid (uniform plan) := by
  constructor
  · intro size; simp [uniform, counting, List.map_map, Function.comp_def]
  · intro size entry member
    obtain ⟨rank, present, rfl⟩ := List.mem_map.mp member
    change (0 : Rat) < 1
    decide
  · intro size; exact total_counting _
  · intro size
    simp only [uniform, massAt]
    by_cases empty : (classRanks plan size).isEmpty = true
    · simp [List.isEmpty_iff.mp empty]
    · simp only [empty]
      exact Rat.natCast_pos.mpr (List.length_pos_iff.mpr (fun nil => empty (by simp [nil])))

/-- A fixed-size source uses the same singleton PlanSized row as resizedStatic. -/
def fixedPlan (size count : Nat) : Plan :=
  .sized (fun found => if found = size then List.replicate count () else []) size

/-- The singleton PlanSized row has no preceding members. -/
theorem fixedPlan_classes (fixed count size : Nat) :
    classRanks (fixedPlan fixed count) size = if size = fixed then List.range count else [] := by
  simp only [fixedPlan, classRanks, PlanVariants.classRanks, PlanVariants.sizedRanks]
  by_cases same : size = fixed
  · subst size
    have offset : PlanVariants.sizedOffset (fun found => if found = fixed then List.replicate count () else []) fixed = 0 := by
      unfold PlanVariants.sizedOffset
      have zeros : (List.range fixed).map (fun found => (if found = fixed then List.replicate count () else []).length) =
          (List.range fixed).map (fun _ => 0) := by
        apply List.map_congr_left
        intro found member
        have different : found ≠ fixed := by have := List.mem_range.mp member; omega
        simp [different]
      rw [zeros]
      induction List.range fixed <;> simp_all
    simp [offset]
  · by_cases within : size ≤ fixed <;> simp [same, within]

/-- The fixed-size row retains the original finite cardinality, including size zero. -/
theorem fixedPlan_count (size total : Nat) : count (fixedPlan size total) = total := by
  have countSum := SourcePlanPartition.class_count_total (fixedPlan size total)
  change ((List.range (size + 1)).map (fun s => (classRanks (fixedPlan size total) s).length)).sum = count (fixedPlan size total) at countSum
  rw [← countSum, List.range_succ, List.map_append, List.sum_append]
  have prefixZero : ((List.range size).map (fun s => (classRanks (fixedPlan size total) s).length)).sum = 0 := by
    have zeros : (List.range size).map (fun s => (classRanks (fixedPlan size total) s).length) =
        (List.range size).map (fun _ => 0) := by
      apply List.map_congr_left
      intro s member
      have different : s ≠ size := by have := List.mem_range.mp member; omega
      simp [fixedPlan_classes, different]
    rw [zeros]
    induction List.range size <;> simp_all
  rw [prefixZero]
  simp [fixedPlan_classes]

/-- Map and shared plans retain all size weights and masses. -/
def mapRecord (record : Record) : Record := { record with plan := .map record.plan }

theorem map_valid (record : Record) (valid : Valid record) : Valid (mapRecord record) := by
  exact ⟨valid.ranks, valid.positive, valid.total, valid.mass⟩

/-- Pay shifts both source class fields by one without changing member ranks. -/
def pay (record : Record) : Record :=
  ⟨.pay record.plan, fun size => match size with | 0 => [] | next + 1 => record.weights next,
    record.retained.map (fun masses size => match size with | 0 => 0 | next + 1 => masses next)⟩

theorem pay_mass (record : Record) (size : Nat) :
    massAt (pay record) (size + 1) = massAt record size := by
  cases found : record.retained <;> simp [pay, massAt, found, classRanks]

theorem pay_mass_zero (record : Record) : massAt (pay record) 0 = 0 := by
  cases found : record.retained <;> simp [pay, massAt, found, classRanks]

/-- No pay can disconnect a size sampler or retained mass from its decoder position. -/
theorem pay_valid (record : Record) (valid : Valid record) : Valid (pay record) := by
  constructor
  · intro size; cases size <;> simp [pay, classRanks, valid.ranks]
  · intro size entry member
    cases size with
    | zero => cases member
    | succ size => exact valid.positive size entry member
  · intro size; cases size <;> simp [pay, classRanks, valid.total, Probability.total]
  · intro size
    cases size with
    | zero =>
        change massAt (pay record) 0 = 0
        exact pay_mass_zero record
    | succ size =>
        change (if (classRanks record.plan size).isEmpty then massAt (pay record) (size + 1) = 0 else 0 < massAt (pay record) (size + 1))
        rw [pay_mass]
        exact valid.mass size

/-- The actual source rank position reads the same complete size-class partition. -/
theorem position_weights (record : Record) (valid : Valid record) (part : SizedRank.Position) (rank : Nat) :
    position record.plan rank = some part ↔ ((record.weights part.size).map Prod.snd)[part.rank]? = some rank := by
  rw [valid.ranks]
  exact SourcePlanPartition.position_iff_lookup record.plan part rank

/-- Every ordinary finite rank has exactly one class and one class position. -/
theorem rank_partition (record : Record) (valid : Valid record) (rank : Nat) :
    (∃ size, rank ∈ (record.weights size).map Prod.snd) ↔ rank < count record.plan := by
  simp only [valid.ranks]
  exact SourcePlanPartition.partition_exact record.plan rank

/-- Nonempty concrete class records satisfy the source relative-weight convention. -/
def classGroup (record : Record) (size : Nat) : Group Nat := ⟨massAt record size, record.weights size⟩

theorem weights_empty (record : Record) (valid : Valid record) (size : Nat) :
    record.weights size = [] ↔ classRanks record.plan size = [] := by
  rw [← valid.ranks size, List.map_eq_nil_iff]

theorem class_valid (record : Record) (valid : Valid record) (size : Nat)
    (nonempty : record.weights size ≠ []) : ValidGroup (classGroup record size) := by
  have ranksNonempty : classRanks record.plan size ≠ [] := fun nil => nonempty ((weights_empty record valid size).mpr nil)
  refine ⟨?_, nonempty, ?_, ?_⟩
  · simpa [classGroup, List.isEmpty_eq_false_iff.mpr ranksNonempty] using valid.mass size
  · exact fun entry member => Rat.le_of_lt (valid.positive size entry member)
  · have lengths := congrArg List.length (valid.ranks size)
    simpa [classGroup, Group.count, List.length_map] using (valid.total size).trans (congrArg Nat.cast lengths.symm)

/-- Retained mass outside every member class is exactly zero. -/
theorem empty_mass (record : Record) (valid : Valid record) (size : Nat)
    (empty : record.weights size = []) : massAt record size = 0 := by
  have noRanks := (weights_empty record valid size).mp empty
  simpa [noRanks] using valid.mass size


/-- Empty classes are omitted from the source's finite size-class tables. -/
def liveGroup (record : Record) (size : Nat) : List (Group Nat) :=
  if (record.weights size).isEmpty then [] else [classGroup record size]

theorem liveGroup_valid (record : Record) (valid : Valid record) (size : Nat)
    (group : Group Nat) (member : group ∈ liveGroup record size) : ValidGroup group := by
  unfold liveGroup at member
  split at member
  · cases member
  · rename_i nonempty
    have same : group = classGroup record size := by simpa using member
    subst group
    exact class_valid record valid size (fun empty => nonempty (by simp [empty]))

theorem liveGroup_ranks (record : Record) (valid : Valid record) (size : Nat) :
    (liveGroup record size).flatMap (fun group => group.weights.map Prod.snd) = classRanks record.plan size := by
  unfold liveGroup
  split
  · rename_i empty
    have empty := List.isEmpty_iff.mp empty
    simpa using ((weights_empty record valid size).mp empty).symm
  · simp [classGroup, valid.ranks]

theorem liveGroup_mass (record : Record) (valid : Valid record) (size : Nat) :
    classMass (liveGroup record size) = massAt record size := by
  unfold liveGroup
  split
  · rename_i empty
    simpa [classMass, branches, branchWeight] using (empty_mass record valid size (List.isEmpty_iff.mp empty)).symm
  · simp [classMass, branches, branchWeight, classGroup, Rat.add_zero]

/-- The actual class weight formula keeps the rank of every source occurrence. -/
theorem classWeights_ranks (groups : List (Group Nat)) :
    (classWeights groups).map Prod.snd = groups.flatMap (fun group => group.weights.map Prod.snd) := by
  simp [classWeights, List.map_flatMap, List.map_map, Function.comp_def]

theorem ranks_count (groups : List (Group Nat)) :
    (groups.flatMap (fun group => group.weights.map Prod.snd)).length = memberCount groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih => simp [memberCount, Group.count, ih]

/-- Construct the source class sampler and optional retained mass table together. -/
def finish (plan : Plan) (groups : Nat → List (Group Nat)) (retain : Bool) : Record :=
  ⟨plan, fun size => classWeights (groups size), if retain then some (fun size => classMass (groups size)) else none⟩

/-- Local live-group proofs derive the complete constructed field invariant. -/
theorem finish_valid (plan : Plan) (groups : Nat → List (Group Nat)) (retain : Bool)
    (ranks : ∀ size, (groups size).flatMap (fun group => group.weights.map Prod.snd) = classRanks plan size)
    (valid : ∀ size group, group ∈ groups size → ValidGroup group)
    (positive : ∀ size group, group ∈ groups size → ∀ entry ∈ group.weights, 0 < entry.1) :
    Valid (finish plan groups retain) := by
  have counts (size : Nat) : memberCount (groups size) = (classRanks plan size).length := by
    rw [← ranks_count, ranks]
  constructor
  · intro size; exact (classWeights_ranks _).trans (ranks size)
  · intro size entry member
    by_cases empty : groups size = []
    · simp [finish, empty, classWeights] at member
    · exact classWeights_positive _ empty (valid size) (positive size) entry member
  · intro size
    by_cases empty : groups size = []
    · have noRanks : classRanks plan size = [] := by simpa [empty] using (ranks size).symm
      simp [finish, empty, noRanks, classWeights, Probability.total]
    · exact (classWeights_total _ empty (valid size)).trans (congrArg Nat.cast (counts size))
  · intro size
    cases retain with
    | false => exact (uniform_valid plan).mass size
    | true =>
        change if (classRanks plan size).isEmpty then classMass (groups size) = 0 else 0 < classMass (groups size)
        by_cases empty : groups size = []
        · have noRanks : classRanks plan size = [] := by simpa [empty] using (ranks size).symm
          simp [empty, noRanks, classMass, branches, branchWeight]
        · have countPositive := memberCount_positive _ empty (valid size)
          rw [counts] at countPositive
          have nonempty := List.length_pos_iff.mp countPositive
          simp only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte]
          exact classMass_positive _ empty (valid size)

/-- Pair records use all nonnegative size splits, including zero on either side. -/
def pairGroups (left right : Record) (size : Nat) : List (Group Nat) :=
  (List.range (size + 1)).flatMap fun split =>
    (liveGroup left split).flatMap fun first =>
      (liveGroup right (size - split)).map fun second =>
        ⟨first.mass * second.mass,
          Probability.map (fun ranks => pairRank (count right.plan) ranks.1 ranks.2)
            (Probability.product first.weights second.weights)⟩

/-- pairBucket preserves a mass table exactly when either child has one. -/
def pair (left right : Record) : Record :=
  finish (.ap left.plan right.plan) (pairGroups left right) (left.retained.isSome || right.retained.isSome)

theorem product_rank_values (left right : Distribution Nat) (rightCount : Nat) :
    (Probability.map (fun ranks => pairRank rightCount ranks.1 ranks.2) (Probability.product left right)).map Prod.snd =
      Decoder.applyValues ((left.map Prod.snd).map (fun first second => pairRank rightCount first second))
        (right.map Prod.snd) := by
  simp [Probability.map, Probability.product, Decoder.applyValues, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]

/-- Live split filtering preserves the exact product class rank order. -/
theorem pairGroups_ranks (left right : Record) (leftValid : Valid left) (rightValid : Valid right) (size : Nat) :
    (pairGroups left right size).flatMap (fun group => group.weights.map Prod.snd) =
      classRanks (.ap left.plan right.plan) size := by
  simp only [pairGroups, List.flatMap_assoc, List.flatMap_map, product_rank_values, classRanks]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro split member
  have leftRanks := liveGroup_ranks left leftValid split
  have rightRanks := liveGroup_ranks right rightValid (size - split)
  unfold liveGroup at *
  split <;> split <;> simp_all [classGroup, Decoder.applyValues]
  rw [← leftRanks, ← rightRanks]
  simp [List.map_map, List.flatMap_map, Function.comp_def]

/-- Every retained size split is a valid concrete product group. -/
theorem pairGroups_valid (left right : Record) (leftValid : Valid left) (rightValid : Valid right)
    (size : Nat) (group : Group Nat) (member : group ∈ pairGroups left right size) : ValidGroup group := by
  obtain ⟨split, _, first, firstMember, second, secondMember, rfl⟩ := by
    simpa only [pairGroups, List.mem_flatMap, List.mem_map] using member
  have valid := pairGroup_valid first second
    (liveGroup_valid left leftValid split first firstMember)
    (liveGroup_valid right rightValid (size - split) second secondMember)
  refine ⟨valid.1, ?_, ?_, ?_⟩
  · simpa [Probability.map, pairGroup] using valid.2.1
  · intro entry present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact valid.2.2.1 original member
  · rw [Probability.total_map]
    simpa [Group.count, Probability.map, pairGroup] using valid.2.2.2

theorem liveGroup_positive (record : Record) (valid : Valid record) (size : Nat)
    (group : Group Nat) (member : group ∈ liveGroup record size) (entry : Rat × Nat)
    (present : entry ∈ group.weights) : 0 < entry.1 := by
  unfold liveGroup at member
  split at member
  · cases member
  · have same : group = classGroup record size := by simpa using member
    subst group
    exact valid.positive size entry present

/-- Pair metadata and the actual pair class sampler satisfy the complete finite field invariant. -/
theorem pair_valid (left right : Record) (leftValid : Valid left) (rightValid : Valid right) : Valid (pair left right) := by
  apply finish_valid
  · exact pairGroups_ranks left right leftValid rightValid
  · exact pairGroups_valid left right leftValid rightValid
  · intro size group member entry present
    obtain ⟨split, _, first, firstMember, second, secondMember, rfl⟩ := by
      simpa only [pairGroups, List.mem_flatMap, List.mem_map] using member
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨leftEntry, leftMember, rightEntry, rightMember, same⟩ := by
      simpa only [Probability.product, List.mem_flatMap, List.mem_map] using member
    cases same
    exact Rat.mul_pos (liveGroup_positive left leftValid split first firstMember leftEntry leftMember)
      (liveGroup_positive right rightValid (size - split) second secondMember rightEntry rightMember)


/-- An offset changes only member positions, never masses or conditional weights. -/
def offsetGroup (offset : Nat) (group : Group Nat) : Group Nat :=
  ⟨group.mass, Probability.map (offset + ·) group.weights⟩

theorem offset_valid (offset : Nat) (group : Group Nat) (valid : ValidGroup group) :
    ValidGroup (offsetGroup offset group) := by
  refine ⟨valid.1, ?_, ?_, ?_⟩
  · simpa [offsetGroup, Probability.map] using valid.2.1
  · intro entry member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact valid.2.2.1 original present
  · change Probability.total (Probability.map _ _) = _
    rw [Probability.total_map]
    simpa [offsetGroup, Group.count, Probability.map] using valid.2.2.2

/-- Ordered frequency plans use the same global offsets as the source n-way plan. -/
def choicePlan : List Record → Plan
  | [] => .select 0
  | record :: rest => .choice record.plan (choicePlan rest)

/-- Each live alternative receives its actual cumulative global-rank offset. -/
def choiceGroups (offset : Nat) : List Record → Nat → List (Group Nat)
  | [], _ => []
  | record :: rest, size => (liveGroup record size).map (offsetGroup offset) ++
      choiceGroups (offset + count record.plan) rest size

/-- The optional class masses follow the source any-isJust test. -/
def choice (records : List Record) : Record :=
  finish (choicePlan records) (choiceGroups 0 records) (records.any (fun record => record.retained.isSome))

theorem choiceGroups_ranks (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (offset size : Nat) :
    (choiceGroups offset records size).flatMap (fun group => group.weights.map Prod.snd) =
      (classRanks (choicePlan records) size).map (offset + ·) := by
  induction records generalizing offset with
  | nil => by_cases same : size = 1 <;> simp [choiceGroups, choicePlan, classRanks, same]
  | cons record rest ih =>
      have tail := ih (fun record member => valid record (by simp [member]))
      simp only [choiceGroups, List.flatMap_append, List.flatMap_map, choicePlan, classRanks,
        List.map_append, tail, List.map_map, Function.comp_def, Nat.add_assoc]
      congr 1
      have front := congrArg (List.map (offset + ·)) (liveGroup_ranks record (valid record (by simp)) size)
      simpa [List.map_flatMap, List.map_map, Function.comp_def, offsetGroup, Probability.map] using front

theorem choiceGroups_valid (records : List Record) (valid : ∀ record ∈ records, Valid record)
    (offset size : Nat) (group : Group Nat) (member : group ∈ choiceGroups offset records size) : ValidGroup group := by
  induction records generalizing offset with
  | nil => cases member
  | cons record rest ih =>
      rcases List.mem_append.mp member with front | tail
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp front
        exact offset_valid offset original (liveGroup_valid record (valid record (by simp)) size original present)
      · exact ih (fun record present => valid record (by simp [present])) _ tail

/-- The source frequency class records are constructed in exact decoder order. -/
theorem choice_valid (records : List Record) (valid : ∀ record ∈ records, Valid record) : Valid (choice records) := by
  apply finish_valid
  · intro size
    simpa using choiceGroups_ranks records valid 0 size
  · exact choiceGroups_valid records valid 0
  · intro size group member entry present
    have positive : ∀ (records : List Record), (∀ record ∈ records, Valid record) → ∀ offset,
        ∀ group ∈ choiceGroups offset records size, ∀ entry ∈ group.weights, 0 < entry.1 := by
      intro records
      induction records with
      | nil => intro valid offset group member; cases member
      | cons record rest ih =>
          intro valid offset group member entry present
          rcases List.mem_append.mp member with front | tail
          · obtain ⟨original, live, rfl⟩ := List.mem_map.mp front
            obtain ⟨originalEntry, member, rfl⟩ := List.mem_map.mp present
            exact liveGroup_positive record (valid record (by simp)) size original live originalEntry member
          · exact ih (fun record member => valid record (by simp [member])) _ group tail entry present
    exact positive records valid 0 group member entry present

/-- Count fallback makes the generic source merge formula exactly retain the child relative weight. -/
theorem count_mass_weight (total inside weight : Rat) (totalNonzero : total ≠ 0) (insideNonzero : inside ≠ 0) :
    mergeWeight total total inside inside weight = weight := by
  simp only [mergeWeight, Rat.div_def]
  calc
    _ = (total * total⁻¹) * (inside * inside⁻¹) * weight := by ac_rfl
    _ = weight := by rw [Rat.mul_inv_cancel _ totalNonzero, Rat.mul_inv_cancel _ insideNonzero]; simp

/-- The generic class constructor equals the actual unweighted branch when all retained masses are absent. -/
theorem count_mass_classes (groups : List (Group Nat))
    (valid : ∀ group ∈ groups, ValidGroup group)
    (countMass : ∀ group ∈ groups, group.mass = (group.count : Rat)) :
    classWeights groups = groups.flatMap Group.weights := by
  by_cases empty : groups = []
  · simp [empty, classWeights]
  have totalNonzero : (memberCount groups : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_pos.mpr (memberCount_positive groups empty valid))
  have massCount : classMass groups = (memberCount groups : Rat) := by
    clear empty totalNonzero
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        have tail := ih (fun group member => valid group (by simp [member]))
          (fun group member => countMass group (by simp [member]))
        change group.mass + classMass rest = ((group.count + memberCount rest : Nat) : Rat)
        rw [countMass group (by simp), tail, Rat.natCast_add]
  simp only [classWeights]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro group member
  have insideNonzero : (group.count : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr (valid group member).2.1))
  rw [massCount, countMass group member]
  have identity : (fun (entry : Rat × Nat) =>
      (mergeWeight (memberCount groups) (memberCount groups) group.count group.count entry.1, entry.2)) = id := by
    funext entry
    rw [count_mass_weight _ _ _ totalNonzero insideNonzero]
    rfl
  rw [identity, List.map_id]

/-- A rebuilt observed member retains its source size and its class weight. -/
def observed (size : Nat) (weight : Rat) : Record :=
  ⟨fixedPlan size 1, fun found => counting (classRanks (fixedPlan size 1) found),
    some (fun found => if found = size then weight else 0)⟩

theorem observed_valid (size : Nat) (weight : Rat) (positive : 0 < weight) : Valid (observed size weight) := by
  have uniform := uniform_valid (fixedPlan size 1)
  refine ⟨uniform.ranks, uniform.positive, uniform.total, ?_⟩
  intro found
  by_cases same : found = size <;> simp [observed, fixedPlan_classes, massAt, same, positive]

/-- Actual class lookup derives the positive weight used by Compile.keyedMember. -/
theorem observe_member_valid (record : Record) (valid : Valid record) (part : SizedRank.Position)
    (rank : Nat) (weight : Rat) (found : (record.weights part.size)[part.rank]? = some (weight, rank)) :
    position record.plan rank = some part ∧ Valid (observed part.size weight) ∧
      count (observed part.size weight).plan = 1 := by
  refine ⟨(position_weights record valid part rank).mpr ?_,
    observed_valid part.size weight (valid.positive _ _ (List.mem_of_getElem? found)), fixedPlan_count _ _⟩
  rw [List.getElem?_map, found]
  rfl


/-- Erase user values while keeping the actual global member order and masses. -/
def rankedMasses (outcomes : Distribution Value) : Distribution Nat :=
  outcomes.zipIdx.map (fun entry => (entry.1.1, entry.2))

theorem rankedMasses_ranks (outcomes : Distribution Value) :
    (rankedMasses outcomes).map Prod.snd = List.range outcomes.length := by
  simpa only [rankedMasses, List.map_map, Function.comp_def, List.range_eq_range'] using List.zipIdx_map_snd 0 outcomes

theorem rankedMasses_total (outcomes : Distribution Value) : total (rankedMasses outcomes) = total outcomes := by
  have preserves : ∀ (items : Distribution Value) (start : Nat),
      total ((items.zipIdx start).map (fun entry => (entry.1.1, entry.2))) = total items := by
    intro items
    induction items with
    | nil => intro start; rfl
    | cons item rest ih => intro start; simp [List.zipIdx_cons, Probability.total, ih]
  exact preserves outcomes 0

/-- staticSampling for an atomic source uses cardinality times its global outcome mass. -/
def atomic (size : Nat) (outcomes : Distribution Value) : Record :=
  ⟨fixedPlan size outcomes.length,
    fun found => if found = size then scale outcomes.length (rankedMasses outcomes) else [], none⟩

/-- A concrete atomic source derives its size weights from its global distribution. -/
theorem atomic_valid (size : Nat) (outcomes : Distribution Value)
    (probability : IsProbability outcomes) (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    Valid (atomic size outcomes) := by
  have nonempty : outcomes ≠ [] := by
    intro empty
    have total := probability.2
    simp [empty, Probability.total] at total
  have countPositive : (0 : Rat) < outcomes.length := Rat.natCast_pos.mpr (List.length_pos_iff.mpr nonempty)
  constructor
  · intro found
    by_cases same : found = size
    · simp [atomic, same, scale, List.map_map, Function.comp_def, rankedMasses_ranks, fixedPlan_classes]
    · simp [atomic, same, fixedPlan_classes]
  · intro found entry member
    by_cases same : found = size
    · simp only [atomic, same, ↓reduceIte] at member
      change entry ∈ scale outcomes.length (rankedMasses outcomes) at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      change original ∈ outcomes.zipIdx.map (fun entry => (entry.1.1, entry.2)) at present
      obtain ⟨indexed, indexMember, indexedEq⟩ := List.mem_map.mp present
      cases indexedEq
      exact Rat.mul_pos countPositive (positive indexed.1 (List.fst_mem_of_mem_zipIdx indexMember))
    · simp [atomic, same] at member
  · intro found
    by_cases same : found = size
    · simp [atomic, same, total_scale, rankedMasses_total, probability.2, fixedPlan_classes, Rat.mul_one]
    · simp [atomic, same, Probability.total, fixedPlan_classes]
  · exact (uniform_valid (fixedPlan size outcomes.length)).mass

/-- Retaining an atomic source keeps its original global conditional law within its one size. -/
theorem atomic_probability (size : Nat) (outcomes : Distribution Value) (nonempty : outcomes ≠ []) :
    scale ((classRanks (atomic size outcomes).plan size).length : Rat)⁻¹
      ((atomic size outcomes).weights size) = rankedMasses outcomes := by
  simp only [atomic, fixedPlan_classes, ↓reduceIte, List.length_range, scale_scale]
  rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr nonempty))), scale_one]

/-- The zero-size operation in pairBucket does not introduce a size class or a rank digit. -/
theorem zero_left_classes (plan : Plan) (size : Nat) :
    classRanks (.ap (fixedPlan 0 1) plan) size = classRanks plan size := by
  simp only [classRanks, List.range_succ_eq_map, List.flatMap_cons, fixedPlan_classes,
    List.flatMap_map]
  simp [Decoder.applyValues, Probability.pairRank]

theorem zero_left_count (plan : Plan) : count (.ap (fixedPlan 0 1) plan) = count plan := by
  simp [count, fixedPlan_count]

/-- The exact chainPlan for the source's zero-size pair operation and two shared arguments. -/
def pairPlan (left right : Plan) : Plan :=
  .ap (.ap (fixedPlan 0 1) (.shared left)) (.shared right)

/-- Shared wrappers and the size-zero operation preserve the binary product class order. -/
theorem pairPlan_classes (left right : Plan) (size : Nat) :
    classRanks (pairPlan left right) size = classRanks (.ap left right) size := by
  unfold pairPlan
  rw [classRanks]
  simp only [zero_left_classes]
  rfl

theorem pairPlan_count (left right : Plan) : count (pairPlan left right) = count left * count right := by
  simp [pairPlan, count, fixedPlan_count]

/-- Source pairBucket's exact decoder plan accompanies the derived sampler and mass fields. -/
def sourcePair (left right : Record) : Record :=
  { pair left right with plan := pairPlan left.plan right.plan }

theorem sourcePair_valid (left right : Record) (leftValid : Valid left) (rightValid : Valid right) :
    Valid (sourcePair left right) := by
  have valid := pair_valid left right leftValid rightValid
  constructor
  · intro size; change _ = classRanks (pairPlan left.plan right.plan) size
    rw [pairPlan_classes]; exact valid.ranks size
  · exact valid.positive
  · intro size; change _ = ((classRanks (pairPlan left.plan right.plan) size).length : Rat)
    rw [pairPlan_classes]; exact valid.total size
  · intro size
    have masses : massAt (sourcePair left right) size = massAt (pair left right) size := by
      unfold massAt
      cases retained : (pair left right).retained with
      | none => simp [sourcePair, retained, pairPlan_classes]; rfl
      | some values => simp [sourcePair, retained]
    rw [masses]
    change if (classRanks (pairPlan left.plan right.plan) size).isEmpty then _ else _
    rw [pairPlan_classes]
    exact valid.mass size

end MicroCFTA.FiniteSizeFields



