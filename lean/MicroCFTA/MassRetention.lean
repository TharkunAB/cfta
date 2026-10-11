import MicroCFTA.RecipeCompile
import MicroCFTA.GeneratorCombinators
import MicroCFTA.SizeTransport

/-!
# Retain observed atomic weights through products

The repaired `Compile.groupBuilt` retains `staticSampling` weights for atomic
and non-atomic sources. A singleton's internal weight is one. Its bucket mass
must carry the original relative member weight when later products remove
the atomic marker. This module derives the resulting merge probabilities.
-/

namespace MicroCFTA.MassRetention
open Probability SizeMass

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- The repaired observation metadata retains every available within-size weight. -/
def observedMember (atomicSource : Bool) (member : RecipeCompile.Member Value) : RecipeCompile.BucketMeta :=
  ⟨member.mass, member.size, 1, atomicSource, member.sizeWeight⟩

/-- The repair does not change a member's probability, size, cardinality, or atomic marker. -/
theorem observed_fields (atomicSource : Bool) (member : RecipeCompile.Member Value) :
    (observedMember atomicSource member).mass = member.mass ∧
    (observedMember atomicSource member).size = member.size ∧
    (observedMember atomicSource member).count = 1 ∧
    (observedMember atomicSource member).atomic = atomicSource ∧
    (observedMember atomicSource member).sizeMass = member.sizeWeight := by
  simp [observedMember]

/-- A non-atomic source follows exactly the existing metadata branch. -/
theorem nonatomic_unchanged (member : RecipeCompile.Member Value) :
    observedMember false member = RecipeCompile.observedMember false member := rfl

/-- Atomic `staticSampling` assigns count times member probability. -/
def atomicWeight (count : Nat) (probability : Rat) : Rat := (count : Rat) * probability

/-- The new explicit weight equals the former atomic fallback in `recursiveGroups`. -/
theorem recursive_atomic_policy (count : Nat) (probability : Rat) (size : Nat) (value : Value) :
    RecipeCompile.bucketSizeMass
      (observedMember true ⟨probability, size, value, some (atomicWeight count probability)⟩) =
      (count : Rat) * probability := rfl

/-- The effective unnormalized members represented by one group's fields. -/
def expand (group : Group α) : Distribution α :=
  scale (group.mass / (group.count : Rat)) group.weights

/-- A reconstructed singleton uses its retained original member weight as the group mass. -/
def singleton (weight : Rat) (value : α) : Group α := ⟨weight, [(1, value)]⟩

/-- Singleton reconstruction retains the exact original member contribution. -/
theorem expand_singleton (weight : Rat) (value : α) : expand (singleton weight value) = [(weight, value)] := by
  simp [expand, singleton, Group.count, scale, Rat.div_def]

/-- Enumerate observed members in their original replay order. -/
def observe (members : Distribution α) : List (Group α) :=
  members.map fun entry => singleton entry.1 entry.2

/-- Expanding observed singleton records gives the original complete weighted stream. -/
theorem expand_observe (members : Distribution α) : (observe members).flatMap expand = members := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      simp only [observe, List.map_cons, List.flatMap_cons, expand_singleton]
      simpa [observe] using congrArg (entry :: ·) ih

/-- Scaling independent sides scales their product by the product of the factors. -/
theorem product_scale (leftFactor rightFactor : Rat) (left : Distribution α) (right : Distribution β) :
    product (scale leftFactor left) (scale rightFactor right) =
      scale (leftFactor * rightFactor) (product left right) := by
  simp only [product, scale, List.flatMap_map, List.map_map, List.map_flatMap]
  apply congrArg (fun f : Rat × α → Distribution (α × β) => left.flatMap f)
  funext first
  apply List.map_congr_left
  intro second _
  simp only [Function.comp_def, Prod.mk.injEq, and_true]
  ac_rfl

/-- Product metadata represents exactly the independent product of its component members. -/
theorem expand_pair (left : Group α) (right : Group β) :
    expand (pairGroup left right) = product (expand left) (expand right) := by
  rw [expand, pairGroup_count]
  change scale ((left.mass * right.mass) / ((left.count * right.count : Nat) : Rat))
    (product left.weights right.weights) = _
  rw [expand, expand, product_scale]
  congr 1
  simp only [Rat.natCast_mul, Rat.div_def, Rat.inv_mul_rev]
  ac_rfl

/-- Expanding all groups is the same unnormalized stream used by the finite merge sampler. -/
theorem expand_mix (groups : List (Group α)) : groups.flatMap expand = mix (branches groups) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change expand group ++ rest.flatMap expand =
        scale group.mass (scale (group.count : Rat)⁻¹ group.weights) ++ mix (branches rest)
      rw [← ih]
      congr 1
      simp [expand, scale_scale, Rat.div_def]

/-- Every valid group's represented members sum to its retained mass. -/
theorem expand_total (group : Group α) (valid : ValidGroup group) : total (expand group) = group.mass := by
  have countNonzero : (group.count : Rat) ≠ 0 :=
    Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr valid.2.1))
  rw [expand, total_scale, valid.2.2.2]
  simp [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ countNonzero]

/-- A merge samples the normalized complete effective member stream. -/
theorem sampler_expansion (groups : List (Group α))
    (valid : ∀ group ∈ groups, ValidGroup group) :
    classSampler groups = normalize (groups.flatMap expand) := by
  have mass : total (groups.flatMap expand) = classMass groups := by
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        simp only [List.flatMap_cons, total_append, classMass, branches, List.map_cons, branchWeight]
        rw [expand_total group (valid group (by simp)), ih (fun g h => valid g (by simp [h]))]
        rfl
  rw [classSampler, frequency, ← expand_mix, normalize, mass]
  rfl

/-- A positive observed member produces a valid one-member group. -/
theorem singleton_valid (weight : Rat) (value : α) (positive : 0 < weight) :
    ValidGroup (singleton weight value) := by
  refine ⟨positive, by simp [singleton], ?_, ?_⟩
  · intro entry present
    have same : entry = (1, value) := by simpa [singleton] using present
    subst entry
    change (0 : Rat) ≤ 1
    decide +kernel
  · simp [singleton, Group.count, total, Rat.add_zero]

/-- The pair groups produced after reading every left member. -/
def observedPairs (members : Distribution α) (right : Group β) : List (Group (α × β)) :=
  (observe members).map fun left => pairGroup left right

/-- Pairing reconstructed members retains the complete independent weighted stream. -/
theorem expand_observedPairs (members : Distribution α) (right : Group β) :
    (observedPairs members right).flatMap expand = product members (expand right) := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      simp only [observedPairs, observe, List.map_cons, List.flatMap_cons, expand_pair, expand_singleton]
      change product [entry] (expand right) ++ (observedPairs rest right).flatMap expand = _
      rw [ih]
      simp [product]

/-- Every observed pair satisfies the internal count/weight invariant. -/
theorem observedPairs_valid (members : Distribution α) (right : Group β)
    (positive : ∀ entry ∈ members, 0 < entry.1) (rightValid : ValidGroup right) :
    ∀ group ∈ observedPairs members right, ValidGroup group := by
  intro group present
  obtain ⟨left, found, rfl⟩ := List.mem_map.mp present
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp found
  exact pairGroup_valid _ _ (singleton_valid _ _ (positive entry member)) rightValid

/-- Reconstructing and pairing all observed members preserves the exact conditional distribution. -/
theorem observed_pair_distribution (members : Distribution α) (right : Group β)
    (positive : ∀ entry ∈ members, 0 < entry.1) (rightValid : ValidGroup right) :
    classSampler (observedPairs members right) = normalize (product members (expand right)) := by
  rw [sampler_expansion _ (observedPairs_valid members right positive rightValid), expand_observedPairs]

/-- The source's atomic count scale is common to every independent product member. -/
theorem product_scale_left (factor : Rat) (left : Distribution α) (right : Distribution β) :
    product (scale factor left) right = scale factor (product left right) := by
  have law := product_scale factor 1 left right
  simpa [scale_one] using law

/-- The repaired path preserves any positive atomic distribution through an ordinary sibling and merge. -/
theorem atomic_observed_pair_distribution (members : Distribution α) (right : Group β)
    (nonempty : members ≠ []) (positive : ∀ entry ∈ members, 0 < entry.1)
    (rightValid : ValidGroup right) :
    classSampler (observedPairs (scale (members.length : Rat) members) right) =
      normalize (product members (expand right)) := by
  have countPositive : (0 : Rat) < members.length := Rat.natCast_pos.mpr (List.length_pos_iff.mpr nonempty)
  rw [observed_pair_distribution]
  · rw [product_scale_left, normalize_scale _ _ (Rat.ne_of_gt countPositive)]
  · intro entry found
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp found
    exact Rat.mul_pos countPositive (positive old present)
  · exact rightValid

/-- The actual repaired pair branch now stores the observed weight times its sibling mass. -/
theorem observed_pair_metadata (mass weight : Rat) (size : Nat) (value : Value)
    (right : RecipeCompile.BucketMeta) :
    (RecipeCompile.pairBucket (observedMember true ⟨mass, size, value, some weight⟩) right).sizeMass =
      some (weight * RecipeCompile.bucketSizeMass right) := by
  simp [RecipeCompile.pairBucket, observedMember, RecipeCompile.bucketSizeMass]

/-- The previous atomic example now keeps the same bounded and unbounded probability. -/
theorem repaired_atomic_pair :
    let left : List (RecipeCompile.Member Bool) :=
      [⟨9 / 10, 1, true, some (9 / 5)⟩, ⟨1 / 10, 1, false, some (1 / 5)⟩]
    let right : RecipeCompile.BucketMeta := ⟨1, 1, 1, false, none⟩
    let paired := left.map fun member => RecipeCompile.payBucket
      (RecipeCompile.pairBucket (observedMember true member) right)
    paired.map RecipeCompile.BucketMeta.size = [3, 3] ∧
      RecipeCompile.firstProbability (paired.map RecipeCompile.BucketMeta.mass) = 9 / 10 ∧
      RecipeCompile.firstProbability (RecipeCompile.mergedSizeMasses paired) = 9 / 10 := by
  decide +kernel

end MicroCFTA.MassRetention
