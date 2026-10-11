import MicroCFTA.MassRetention
import MicroCFTA.SamplerReplay

/-!
# Observation partitions and guarded bucket products

This model connects normalized bucket fields to the weighted member stream.
Key partitions and product groups are constructed. Their homogeneity and
coverage are proved, so testing a guard once per key pair preserves the
complete conditional distribution.
-/

namespace MicroCFTA.ObservationMass
open Probability SizeMass MassRetention

/-- Bucket normalization is an exact representation of its original weighted members. -/
theorem expand_bucket (members : Distribution α) (nonempty : members ≠ [])
    (nonzero : total members ≠ 0) : expand (bucket members) = members := by
  have factor : expand (bucket members) =
      scale (bucket members).mass (scale ((bucket members).count : Rat)⁻¹ (bucket members).weights) := by
    simp [expand, scale_scale, Rat.div_def]
  rw [factor, bucket_conditional members nonempty]
  exact restore_normalized members nonzero

/-- The constructed observation buckets retain every original weighted occurrence. -/
theorem split_expansion [DecidableEq Key] (key : α → Key) (members : Distribution α)
    (positive : ∀ entry ∈ members, 0 < entry.1) :
    ((splitClass (fun entry => key entry.2) members).flatMap expand).Perm members := by
  have same : (splitClass (fun entry => key entry.2) members).flatMap expand =
      (Sized.groups (fun entry => key entry.2) members).flatten := by
    simp only [splitClass, List.flatMap_def]
    apply congrArg List.flatten
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (Sized.groups (fun entry => key entry.2) members)]
    apply List.map_congr_left
    intro part present
    obtain ⟨first, rest, shape, _⟩ := Sized.groups_constant (fun entry => key entry.2) members part present
    have nonempty : part ≠ [] := by simp [shape]
    apply expand_bucket part nonempty
    apply Rat.ne_of_gt
    apply Sized.total_positive part nonempty
    intro entry found
    exact positive entry ((Sized.groups_perm (fun entry => key entry.2) members).mem_iff.mp
      (List.mem_flatten.mpr ⟨part, present, found⟩))
  rw [same]
  exact Sized.groups_perm _ _

/-- Relative internal bucket weights have the same observation key as their raw members. -/
theorem split_uniform [DecidableEq Key] (key : α → Key) (members : Distribution α)
    (group : Group α) (present : group ∈ splitClass (fun entry => key entry.2) members) :
    ∃ observed, ∀ entry ∈ group.weights, key entry.2 = observed := by
  obtain ⟨part, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨first, rest, shape, sameKey⟩ := Sized.groups_constant (fun entry => key entry.2) members part member
  refine ⟨key first.2, ?_⟩
  intro entry found
  obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp found
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp innerMember
  exact sameKey original originalMember

/-- Construct every pair of observation buckets in source group order. -/
def pairGroups (left : List (Group α)) (right : List (Group β)) : List (Group (α × β)) :=
  left.flatMap fun first => right.map (pairGroup first)

/-- Pair bucket fields represent exactly the original product, up to grouping order. -/
theorem pair_expansion (left : List (Group α)) (right : List (Group β)) :
    ((pairGroups left right).flatMap expand).Perm
      (product (left.flatMap expand) (right.flatMap expand)) := by
  have same : (pairGroups left right).flatMap expand =
      GeneratorCombinators.groupProducts (left.map expand) (right.map expand) := by
    simp [pairGroups, GeneratorCombinators.groupProducts, List.flatMap_assoc,
      List.flatMap_map, expand_pair]
  rw [same]
  simpa [List.flatMap_def] using GeneratorCombinators.groupProducts_perm (left.map expand) (right.map expand)

/-- All members of a product of key-homogeneous buckets have one guard result. -/
theorem pair_uniform (leftKey : α → LeftKey) (rightKey : β → RightKey)
    (relation : LeftKey → RightKey → Bool) (left : Group α) (right : Group β)
    (leftUniform : ∃ observed, ∀ entry ∈ left.weights, leftKey entry.2 = observed)
    (rightUniform : ∃ observed, ∀ entry ∈ right.weights, rightKey entry.2 = observed) :
    ∃ result, ∀ entry ∈ (pairGroup left right).weights,
      relation (leftKey entry.2.1) (rightKey entry.2.2) = result := by
  obtain ⟨lk, lh⟩ := leftUniform
  obtain ⟨rk, rh⟩ := rightUniform
  refine ⟨relation lk rk, ?_⟩
  intro entry present
  obtain ⟨first, found, second, belongs, same⟩ := (by simpa [pairGroup, product] using present :
    ∃ first, first ∈ left.weights ∧ ∃ second, second ∈ right.weights ∧
      (first.1 * second.1, (first.2, second.2)) = entry)
  subst entry
  simp [lh first found, rh second belongs]

/-- A homogeneous nonempty bucket needs one guard decision on its first member. -/
def accepted (predicate : α → Bool) (group : Group α) : Bool :=
  (group.weights.head?.map (fun entry => predicate entry.2)).getD false

/-- A bucket-level guard decision retains exactly its accepted weighted members. -/
theorem restrict_group (predicate : α → Bool) (group : Group α) (nonempty : group.weights ≠ [])
    (uniform : ∃ result, ∀ entry ∈ group.weights, predicate entry.2 = result) :
    restrict predicate (expand group) = if accepted predicate group then expand group else [] := by
  obtain ⟨result, same⟩ := uniform
  have verdict : accepted predicate group = result := by
    cases weights : group.weights with
    | nil => exact False.elim (nonempty weights)
    | cons first rest =>
        simp only [accepted, weights, List.head?_cons, Option.map_some, Option.getD_some]
        exact same first (by simp [weights])
  have expanded : ∀ entry ∈ expand group, predicate entry.2 = result := by
    intro entry present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact same original member
  rw [verdict]
  cases result
  · simp only [Bool.false_eq_true, ↓reduceIte, restrict]
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    simp [expanded entry member]
  · simp only [↓reduceIte, restrict]
    exact List.filter_eq_self.mpr expanded

/-- Filtering homogeneous buckets commutes exactly with expanding their weighted members. -/
theorem filter_expansion (predicate : α → Bool) (groups : List (Group α))
    (nonempty : ∀ group ∈ groups, group.weights ≠ [])
    (uniform : ∀ group ∈ groups, ∃ result, ∀ entry ∈ group.weights, predicate entry.2 = result) :
    ((groups.filter (accepted predicate)).flatMap expand) = restrict predicate (groups.flatMap expand) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have later := ih (fun other member => nonempty other (by simp [member]))
        (fun other member => uniform other (by simp [member]))
      change ((group :: rest).filter (accepted predicate)).flatMap expand =
        (expand group ++ rest.flatMap expand).filter (fun entry => predicate entry.2)
      rw [List.filter_append]
      rw [show (expand group).filter (fun entry => predicate entry.2) =
        if accepted predicate group then expand group else [] from
          restrict_group predicate group (nonempty group (by simp)) (uniform group (by simp))]
      cases selected : accepted predicate group <;> simp [selected, later, restrict]

/-- Observation partitions are paired and filtered before the source merge normalizes their masses. -/
def guardedGroups [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β) : List (Group (α × β)) :=
  (pairGroups (splitClass (fun entry => leftKey entry.2) left) (splitClass (fun entry => rightKey entry.2) right)).filter
    (accepted (fun pair => relation (leftKey pair.1) (rightKey pair.2)))

/-- Guarded product buckets retain all and only the original accepted weighted pairs. -/
theorem guarded_expansion [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    ((guardedGroups leftKey rightKey relation left right).flatMap expand).Perm
      (restrict (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)) := by
  let leftGroups := splitClass (fun entry => leftKey entry.2) left
  let rightGroups := splitClass (fun entry => rightKey entry.2) right
  let groups := pairGroups leftGroups rightGroups
  have allValid : ∀ group ∈ groups, ValidGroup group := by
    intro group present
    obtain ⟨first, member, second, found, same⟩ := (by simpa [groups, pairGroups] using present :
      ∃ first, first ∈ leftGroups ∧ ∃ second, second ∈ rightGroups ∧ pairGroup first second = group)
    subst group
    exact pairGroup_valid _ _ (splitClass_valid _ left leftPositive first member)
      (splitClass_valid _ right rightPositive second found)
  have homogeneous : ∀ group ∈ groups, ∃ result, ∀ entry ∈ group.weights,
      relation (leftKey entry.2.1) (rightKey entry.2.2) = result := by
    intro group present
    obtain ⟨first, member, second, found, same⟩ := (by simpa [groups, pairGroups] using present :
      ∃ first, first ∈ leftGroups ∧ ∃ second, second ∈ rightGroups ∧ pairGroup first second = group)
    subst group
    exact pair_uniform leftKey rightKey relation first second
      (split_uniform leftKey left first member) (split_uniform rightKey right second found)
  change ((groups.filter _).flatMap expand).Perm _
  rw [filter_expansion _ groups (fun group member => (allValid group member).2.1) homogeneous]
  apply List.Perm.filter
  exact (pair_expansion leftGroups rightGroups).trans
    (GeneratorCombinators.product_perm (split_expansion leftKey left leftPositive) (split_expansion rightKey right rightPositive))

/-- Every retained product bucket satisfies the actual mass/count normalization invariant. -/
theorem guarded_valid [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    ∀ group ∈ guardedGroups leftKey rightKey relation left right, ValidGroup group := by
  intro group present
  obtain ⟨first, member, second, found, same⟩ :=
    (by simpa [guardedGroups, pairGroups] using (List.mem_filter.mp present).1 :
      ∃ first, first ∈ splitClass (fun entry => leftKey entry.2) left ∧
        ∃ second, second ∈ splitClass (fun entry => rightKey entry.2) right ∧ pairGroup first second = group)
  subst group
  exact pairGroup_valid _ _ (splitClass_valid _ left leftPositive first member)
    (splitClass_valid _ right rightPositive second found)

/-- General observation/product/guard/merge compilation preserves the exact conditional distribution. -/
theorem guarded_distribution [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1)
    (event : α × β → Bool) :
    eventMass event (classSampler (guardedGroups leftKey rightKey relation left right)) =
      eventMass event (condition (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)) := by
  rw [sampler_expansion _ (guarded_valid leftKey rightKey relation left right leftPositive rightPositive)]
  exact normalized_perm_event event (guarded_expansion leftKey rightKey relation left right leftPositive rightPositive)

/-- Expansion retains one array position per stored weight, independently of the weight magnitude. -/
theorem expansion_count (groups : List (Group α)) : (groups.flatMap expand).length = memberCount groups := by
  induction groups with
  | nil => rfl
  | cons first rest ih => simp [List.flatMap_cons, memberCount, ih, expand, scale, Group.count]

/-- Guarded bucket counts equal the number of accepted Cartesian member pairs. -/
theorem guarded_count [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    memberCount (guardedGroups leftKey rightKey relation left right) =
      (restrict (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)).length := by
  rw [← expansion_count]
  exact (guarded_expansion leftKey rightKey relation left right leftPositive rightPositive).length_eq

/-- Reading positive raw members produces strictly positive relative bucket weights. -/
theorem split_positive [DecidableEq Key] (key : α → Key) (members : Distribution α)
    (positive : ∀ entry ∈ members, 0 < entry.1) (group : Group α)
    (present : group ∈ splitClass (fun entry => key entry.2) members) :
    ∀ entry ∈ group.weights, 0 < entry.1 := by
  obtain ⟨part, found, rfl⟩ := List.mem_map.mp present
  obtain ⟨first, rest, shape, _⟩ := Sized.groups_constant (fun entry => key entry.2) members part found
  have nonempty : part ≠ [] := by simp [shape]
  have partPositive : ∀ entry ∈ part, 0 < entry.1 := by
    intro entry member
    exact positive entry ((Sized.groups_perm (fun entry => key entry.2) members).mem_iff.mp
      (List.mem_flatten.mpr ⟨part, found, member⟩))
  intro entry member
  obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp innerMember
  exact Rat.mul_pos (Rat.natCast_pos.mpr (List.length_pos_iff.mpr nonempty))
    (Rat.mul_pos (Rat.inv_pos.mpr (Sized.total_positive part nonempty partPositive)) (partPositive original originalMember))

/-- Retained guarded pairs have strictly positive weight at every replay position. -/
theorem guarded_positive [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    ∀ group ∈ guardedGroups leftKey rightKey relation left right, ∀ entry ∈ group.weights, 0 < entry.1 := by
  intro group present
  obtain ⟨first, member, second, found, same⟩ :=
    (by simpa [guardedGroups, pairGroups] using (List.mem_filter.mp present).1 :
      ∃ first, first ∈ splitClass (fun entry => leftKey entry.2) left ∧
        ∃ second, second ∈ splitClass (fun entry => rightKey entry.2) right ∧ pairGroup first second = group)
  subst group
  intro entry present
  obtain ⟨le, lm, re, rm, same⟩ := (by simpa [pairGroup, product] using present :
    ∃ le, le ∈ first.weights ∧ ∃ re, re ∈ second.weights ∧ (le.1 * re.1, (le.2, re.2)) = entry)
  subst entry
  exact Rat.mul_pos (split_positive leftKey left leftPositive first member le lm)
    (split_positive rightKey right rightPositive second found re rm)

/-- Build independent decoder and sampler fields for the normalized bucket merge. -/
def mergeRecord (groups : List (Group α)) : SamplerReplay.Record α :=
  SamplerReplay.manyRecord (groups.map fun group => (group.mass, SamplerReplay.source group.weights))

/-- The record sampler uses precisely the bucket mass and internal weight distribution. -/
theorem mergeRecord_distribution (groups : List (Group α)) (valid : ∀ group ∈ groups, ValidGroup group) :
    (mergeRecord groups).sampling.values = classSampler groups := by
  rw [mergeRecord, SamplerReplay.many_values]
  simp only [List.map_map, Function.comp_def, SamplerReplay.source, Decoder.count, List.length_map,
    SamplerReplay.weightedChoice, List.filterMap_map]
  have branchesEq : groups.filterMap
      (fun group => if 0 < group.weights.length ∧ 0 < group.mass then
        some (group.mass, normalize group.weights) else none) = branches groups := by
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        have invariant := valid group (by simp)
        have countPositive := List.length_pos_iff.mpr invariant.2.1
        simp only [List.filterMap_cons, countPositive, invariant.1, and_self, ↓reduceIte, branches, List.map_cons]
        congr 1
        · simp only [normalize, invariant.2.2.2]
        · exact ih (fun other member => valid other (by simp [member]))
  exact congrArg frequency branchesEq

/-- Positive valid bucket fields derive a complete record invariant for their merge. -/
theorem mergeRecord_live (groups : List (Group α))
    (valid : ∀ group ∈ groups, ValidGroup group)
    (positive : ∀ group ∈ groups, ∀ entry ∈ group.weights, 0 < entry.1) :
    SamplerReplay.LiveValid (mergeRecord groups) := by
  apply SamplerReplay.many_live
  · intro entry present
    obtain ⟨group, member, rfl⟩ := List.mem_map.mp present
    exact SamplerReplay.source_live group.weights (positive group member)
  · intro entry present _
    obtain ⟨group, member, rfl⟩ := List.mem_map.mp present
    exact (valid group member).1

/-- The guarded compiler's completed record has exact replay, positive coverage, and normalized live mass. -/
theorem guarded_record_live [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    SamplerReplay.LiveValid (mergeRecord (guardedGroups leftKey rightKey relation left right)) :=
  mergeRecord_live _ (guarded_valid leftKey rightKey relation left right leftPositive rightPositive)
    (guarded_positive leftKey rightKey relation left right leftPositive rightPositive)

/-- The compiler record retains the exact accepted member multiset, including repeated output values. -/
theorem guarded_record_members [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    (Decoder.values (mergeRecord (guardedGroups leftKey rightKey relation left right)).plan).Perm
      ((restrict (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)).map Prod.snd) := by
  have projection := (guarded_expansion leftKey rightKey relation left right leftPositive rightPositive).map Prod.snd
  simpa [mergeRecord, SamplerReplay.manyRecord, SamplerReplay.manyPlan_values,
    SamplerReplay.source, Decoder.values, List.flatMap_map, List.map_flatMap,
    expand, scale, List.map_map, Function.comp_def] using projection

/-- The guarded compiler record's count is the exact number of accepted input member pairs. -/
theorem guarded_record_count [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1) :
    Decoder.count (mergeRecord (guardedGroups leftKey rightKey relation left right)).plan =
      (restrict (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)).length := by
  rw [Decoder.count_correct]
  simpa using (guarded_record_members leftKey rightKey relation left right leftPositive rightPositive).length_eq

/-- The independently built compiler sampler implements the declared guarded product distribution. -/
theorem guarded_record_probability [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1)
    (event : α × β → Bool) :
    eventMass event (mergeRecord (guardedGroups leftKey rightKey relation left right)).sampling.values =
      eventMass event (condition (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)) := by
  rw [mergeRecord_distribution _ (guarded_valid leftKey rightKey relation left right leftPositive rightPositive)]
  exact guarded_distribution leftKey rightKey relation left right leftPositive rightPositive event

/-- Positive sampled compiler members are all and only the guard's admitted input pairs. -/
theorem guarded_record_exact [DecidableEq LeftKey] [DecidableEq RightKey]
    (leftKey : α → LeftKey) (rightKey : β → RightKey) (relation : LeftKey → RightKey → Bool)
    (left : Distribution α) (right : Distribution β)
    (leftPositive : ∀ entry ∈ left, 0 < entry.1) (rightPositive : ∀ entry ∈ right, 0 < entry.1)
    (value : α × β) :
    value ∈ ((restrict (fun pair => relation (leftKey pair.1) (rightKey pair.2)) (product left right)).map Prod.snd) ↔
      ∃ rank mass, 0 < mass ∧ (mass, (rank, value)) ∈
        (mergeRecord (guardedGroups leftKey rightKey relation left right)).sampling.ranked := by
  have perm := guarded_record_members leftKey rightKey relation left right leftPositive rightPositive
  have valid := guarded_record_live leftKey rightKey relation left right leftPositive rightPositive
  constructor
  · intro present
    obtain ⟨rank, within, decoded⟩ := (Decoder.mem_values_iff _ value).mp (perm.mem_iff.mpr present)
    obtain ⟨mass, found, positive, member, selected⟩ := valid.2.1 rank within
    have same : found = value := Option.some.inj (selected.symm.trans decoded)
    subst found
    exact ⟨rank, mass, positive, member⟩
  · rintro ⟨rank, mass, _, member⟩
    have decoded := valid.1.2 _ member
    exact perm.mem_iff.mp ((Decoder.mem_values_iff _ value).mpr
      ⟨rank, SamplerReplay.decoded_bound _ _ _ decoded, decoded⟩)

end MicroCFTA.ObservationMass
