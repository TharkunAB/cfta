import MicroCFTA.RecursiveJoinRuntime
import MicroCFTA.RecursiveRecord
import MicroCFTA.MassRetention

/-!
# Uniform recursive runtime rank laws

The unweighted route is justified by local count-mass and uniform-rank
properties. These laws retain replay ranks, including when values repeat.
They do not infer a probability law from a Boolean marker alone.
-/
namespace MicroCFTA.RecursiveUniformRuntime
open Probability SamplerReplay RecursiveRankMass

/-- Every replay rank receives its uniform share in the complete ordered law. -/
def Uniform (record : Record Value) : Prop :=
  rankMass record = Sampler.uniformRanks (Decoder.count record.plan)

/-- An ordinary recursive key has count mass and a uniform conditional rank law. -/
def CountedUniform (group : GroupedRecord.Group Value) : Prop :=
  group.mass = (Decoder.count group.members.plan : Rat) ∧ Uniform group.members

/-- The source cached-decoder uniform sampler supplies the local rank law directly. -/
theorem uniform_record (plan : Decoder.Plan Value) (fallback : Value) :
    Uniform (RecursiveRecord.uniformRecord plan fallback) := by
  simp [Uniform, rankMass, RecursiveRecord.uniformRecord, Sampler.uniformSampler,
    Probability.map, List.map_map, Function.comp_def]

/-- Mapping values cannot change uniform replay ranks. -/
theorem uniform_map (transform : Value → Result) (record : Record Value) (uniform : Uniform record) :
    Uniform (mapRecord transform record) := by
  change rankMass (mapRecord transform record) = _
  rw [map_rankMass]
  exact uniform

/-- Independent normalization commutes with product, including empty distributions. -/
theorem product_normalize (left : Distribution A) (right : Distribution B) :
    product (normalize left) (normalize right) = normalize (product left right) := by
  simp only [normalize, MassRetention.product_scale, total_product, Rat.inv_mul_rev]
  rw [Rat.mul_comm]

/-- A product of unit masses is the unit mass list of all ordered pairs. -/
theorem product_counting (left : List A) (right : List B) :
    product (counting left) (counting right) = counting (left.flatMap fun a => right.map fun b => (a, b)) := by
  simp [product, counting, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

/-- Mixed-radix product order enumerates the complete consecutive rank interval. -/
theorem pair_ranges (left right : Nat) :
    (List.range left).flatMap (fun first => (List.range right).map (pairRank right first)) = List.range (left * right) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ih]
      change List.range (left * right) ++ (List.range right).map (fun index => left * right + index) = _
      rw [← List.range'_eq_map_range]
      simpa only [List.range_eq_range', Nat.zero_add, Nat.succ_mul] using
        (List.range'_append_1 (s := 0) (m := left * right) (n := right))

/-- Independent uniform rank choices give the uniform product rank law. -/
theorem product_uniform_ranks (left right : Nat) :
    Probability.map (fun pair => pairRank right pair.1 pair.2)
      (product (Sampler.uniformRanks left) (Sampler.uniformRanks right)) =
      Sampler.uniformRanks (left * right) := by
  rw [Sampler.uniformRanks, Sampler.uniformRanks, product_normalize, product_counting,
    Sampler.map_normalize, Sampler.map_counting]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  rw [pair_ranges]
  rfl

/-- The actual applicative product sampler preserves uniform replay ranks. -/
theorem uniform_apply (functions : Record (A → B)) (arguments : Record A)
    (left : Uniform functions) (right : Uniform arguments) : Uniform (applyRecord functions arguments) := by
  change rankMass (applyRecord functions arguments) = _
  rw [apply_rankMass, left, right]
  exact product_uniform_ranks _ _

/-- Value mapping preserves both source properties used by the unweighted route. -/
theorem counted_map (transform : Value → Result) (group : GroupedRecord.Group Value)
    (uniform : CountedUniform group) : CountedUniform (GroupedRecord.map transform group) :=
  ⟨uniform.1, uniform_map transform group.members uniform.2⟩

/-- One product split multiplies counts and masses and retains a uniform rank law. -/
theorem counted_apply (functions : GroupedRecord.Group (A → B)) (arguments : GroupedRecord.Group A)
    (left : CountedUniform functions) (right : CountedUniform arguments) :
    CountedUniform (GroupedRecord.apply functions arguments) := by
  refine ⟨?_, uniform_apply _ _ left.2 right.2⟩
  simp [GroupedRecord.apply, applyRecord, Decoder.count, left.1, right.1]

/-- Add source record counts in branch order. -/
def totalCount : List (Record Value) → Nat
  | [] => 0
  | record :: rest => Decoder.count record.plan + totalCount rest

/-- The disjoint rank intervals retain offsets through empty branches. -/
def intervals (offset : Nat) : List (Record Value) → List (List Nat)
  | [] => []
  | record :: rest => List.range' offset (Decoder.count record.plan) ::
      intervals (offset + Decoder.count record.plan) rest

/-- All intervals form one consecutive source rank range. -/
theorem intervals_flatten (offset : Nat) (records : List (Record Value)) :
    (intervals offset records).flatten = List.range' offset (totalCount records) := by
  induction records generalizing offset with
  | nil => simp [intervals, totalCount]
  | cons record rest ih =>
      simp only [intervals, List.flatten_cons, ih, totalCount]
      exact List.range'_append_1

/-- Count-mass choice branches have exactly the source total cardinality. -/
theorem many_count (records : List (Record Value)) :
    Decoder.count (manyRecord (records.map fun record => ((Decoder.count record.plan : Rat), record))).plan =
      totalCount records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simpa only [manyRecord, List.map_cons, manyPlan, Decoder.count, totalCount] using
        congrArg (Decoder.count record.plan + ·) ih

/-- The actual choice worker uses count-weighted uniform distributions over its exact rank intervals. -/
theorem rows_uniform (offset : Nat) (records : List (Record Value))
    (uniform : ∀ record ∈ records, Uniform record) :
    rankRows offset (records.map fun record => ((Decoder.count record.plan : Rat), record)) =
      RecursiveRecord.countingParts (intervals offset records) := by
  induction records generalizing offset with
  | nil => rfl
  | cons record rest ih =>
      have tail := ih (offset + Decoder.count record.plan) (fun other member => uniform other (by simp [member]))
      have head := uniform record (by simp)
      unfold Uniform at head
      simp only [List.map_cons, rankRows, intervals, RecursiveRecord.countingParts,
        List.filterMap_cons, List.length_range', Rat.natCast_pos, and_self]
      rw [tail]
      by_cases live : 0 < Decoder.count record.plan
      · simp only [live, ↓reduceIte, head, Sampler.uniformRanks, Sampler.map_normalize, Sampler.map_counting]
        rw [← List.range'_eq_map_range]
        rfl
      · simp [live, RecursiveRecord.countingParts]

/-- Uniform source classes chosen by counts retain uniform global replay ranks. -/
theorem uniform_many (records : List (Record Value)) (uniform : ∀ record ∈ records, Uniform record) :
    Uniform (manyRecord (records.map fun record => ((Decoder.count record.plan : Rat), record))) := by
  unfold Uniform
  rw [many_count, many_rankMass, rows_uniform 0 records uniform]
  rw [frequency, (RecursiveRecord.counting_parts_exact (intervals 0 records)).1,
    (RecursiveRecord.counting_parts_exact (intervals 0 records)).2, intervals_flatten]
  simp [Sampler.uniformRanks, normalize, total_counting, List.range_eq_range']

/-- Merging count-mass groups has count mass without any probability assumption. -/
theorem merge_count_mass (groups : List (GroupedRecord.Group Value))
    (counted : ∀ group ∈ groups, group.mass = (Decoder.count group.members.plan : Rat)) :
    (GroupedRecord.merge groups).mass = (Decoder.count (GroupedRecord.merge groups).members.plan : Rat) := by
  rw [GroupedRecord.merge_count]
  change GroupedRecord.massSum groups = (GroupedRecord.countSum groups : Rat)
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [GroupedRecord.massSum, GroupedRecord.countSum, Rat.natCast_add]
      rw [counted group (by simp), ih (fun other member => counted other (by simp [member]))]

/-- Source same-key merging preserves both local requirements of the unweighted path. -/
theorem counted_merge (groups : List (GroupedRecord.Group Value))
    (uniform : ∀ group ∈ groups, CountedUniform group) : CountedUniform (GroupedRecord.merge groups) := by
  refine ⟨merge_count_mass groups (fun group member => (uniform group member).1), ?_⟩
  have rows : groups.map (fun group => (group.mass, group.members)) =
      (groups.map GroupedRecord.Group.members).map (fun record => ((Decoder.count record.plan : Rat), record)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro group member
    rw [(uniform group member).1]
    rfl
  change Uniform (manyRecord _)
  rw [rows]
  apply uniform_many
  intro record member
  obtain ⟨group, present, rfl⟩ := List.mem_map.mp member
  exact (uniform group present).2

/-- The source product's size-split chooser preserves count mass and uniform ranks. -/
theorem counted_product (functions : GroupedRecord.Classes (A → B)) (arguments : GroupedRecord.Classes A)
    (left : ∀ size, CountedUniform (functions size)) (right : ∀ size, CountedUniform (arguments size)) :
    ∀ size, CountedUniform (GroupedRecord.productClasses functions arguments size) := by
  intro size
  apply counted_merge
  intro group member
  obtain ⟨split, _, rfl⟩ := List.mem_map.mp member
  exact counted_apply _ _ (left split) (right (size - split))

/-- Unit-mass source records have uniform ranks even when their values repeat. -/
theorem uniform_counting (values : List Value) : Uniform (SamplerReplay.source (counting values)) := by
  have ranks : Probability.map Prod.fst (rankedSource (counting values)) =
      FiniteSizeFields.rankedMasses (counting values) := by
    simp [Probability.map, rankedSource, FiniteSizeFields.rankedMasses, List.map_map, Function.comp_def]
  have common := StaticSamplingDispatch.common_mass_ranks (counting values) 1 (by
    intro entry member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    rfl)
  unfold Uniform rankMass
  simp only [SamplerReplay.source, Sampler.map_normalize, ranks, common, scale_one]
  simp [counting, Decoder.count, Sampler.uniformRanks]

/-- The absent class has zero count mass and the empty uniform rank law. -/
theorem counted_empty : CountedUniform (GroupedRecord.empty : GroupedRecord.Group Value) :=
  ⟨rfl, uniform_counting []⟩

/-- Only finite leaf fields need local unweighted laws. Recursive occurrences
and composite constructors add no new probability premise. -/
def Leaves : KeyedSource.Recipe Key Root Value → Prop
  | .finite source => ∀ size, Uniform (FiniteSource.atSize source size)
  | .retained mass _ source => ∀ size,
      CountedUniform (GroupedRecord.retained (mass size) (FiniteSource.atSize source size))
  | .occurrence _ => True
  | .map _ inner | .pay inner => Leaves inner
  | .choice left right | .ap left right => Leaves left ∧ Leaves right

/-- Every complete body derives count mass and uniform ranks from its finite
leaves and recursive child fields. -/
theorem record_uniform (recipe : KeyedSource.Recipe Key Root Value)
    (leaves : Leaves recipe) (environment : Key → GroupedRecord.Classes Root)
    (roots : ∀ key size, CountedUniform (environment key size)) (size : Nat) :
    CountedUniform (KeyedSource.record recipe environment size) := by
  induction recipe generalizing size with
  | finite source => exact ⟨rfl, leaves size⟩
  | retained mass positive source => exact leaves size
  | occurrence key => exact roots key size
  | map transform inner ih => exact counted_map transform _ (ih leaves size)
  | pay inner ih => cases size with
    | zero => exact counted_empty
    | succ size => exact ih leaves size
  | choice left right ihl ihr =>
      apply counted_merge
      intro group member
      rcases List.mem_cons.mp member with rfl | other
      · exact ihl leaves.1 size
      · have same := List.mem_singleton.mp other
        subst group
        exact ihr leaves.2 size
  | ap functions arguments ihf iha =>
      exact counted_product _ _ (ihf leaves.1) (iha leaves.2) size

/-- Size induction closes the simultaneous family law for every key. No
whole-family uniformity or sampler correspondence is a premise. -/
theorem family_uniform (program : Key → KeyedSource.Recipe Key Root Root)
    (leaves : ∀ key, Leaves (program key)) (size : Nat) (key : Key) :
    CountedUniform (KeyedSource.family program size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.family]
      apply record_uniform _ (leaves key)
      intro childKey childSize
      split
      · next smaller => exact ih childSize smaller childKey
      · exact counted_empty

/-- The bounded source sampler is uniform when its exact classes are uniform;
class selection uses counts even when key masses are otherwise retained. -/
theorem bounded_uniform (classes : GroupedRecord.Classes Value)
    (uniform : ∀ size, Uniform (classes size).members) (bound : Nat) :
    Uniform (GroupedRecord.bounded classes bound) := by
  change Uniform (manyRecord _)
  have rows : (List.range (bound + 1)).map (fun size =>
        ((Decoder.count (classes size).members.plan : Rat), (classes size).members)) =
      ((List.range (bound + 1)).map fun size => (classes size).members).map
        (fun record => ((Decoder.count record.plan : Rat), record)) := by
    simp [List.map_map, Function.comp_def]
  rw [rows]
  apply uniform_many
  intro record member
  obtain ⟨size, _, rfl⟩ := List.mem_map.mp member
  exact uniform size

/-- The actual unweighted runtime branch preserves the complete ordered rank
law of the full recursive family, under finite leaf laws only. -/
theorem unweighted_family_rankLaw (program : Key → KeyedSource.Recipe Key Root Root)
    (leaves : ∀ key, Leaves (program key)) (key : Key) (bound : Nat) :
    rankMass (RecursiveJoinRuntime.boundedSampler false (fun size => KeyedSource.family program size key) bound) =
      rankMass (GroupedRecord.bounded (fun size => KeyedSource.family program size key) bound) := by
  have actual := bounded_uniform (fun size => KeyedSource.family program size key)
    (fun size => (family_uniform program leaves size key).2) bound
  have direct := uniform_counting (Decoder.values
    (GroupedRecord.bounded (fun size => KeyedSource.family program size key) bound).plan)
  unfold Uniform at actual direct
  change rankMass (SamplerReplay.source _) = _
  rw [direct, actual]
  congr 1
  simp [SamplerReplay.source, counting, Decoder.count_correct, Decoder.values, Function.comp_def]

/-- Rank coherence upgrades the unweighted law to exact value-and-rank
probabilities, without identifying equal member values. -/
theorem unweighted_family_ranked (program : Key → KeyedSource.Recipe Key Root Root)
    (leaves : ∀ key, Leaves (program key)) (key : Key) (bound : Nat) :
    (RecursiveJoinRuntime.boundedSampler false (fun size => KeyedSource.family program size key) bound).sampling.ranked =
      (GroupedRecord.bounded (fun size => KeyedSource.family program size key) bound).sampling.ranked := by
  have replay := ranked_projection id _ _ _ _
    (source_coherent (counting (Decoder.values
      (GroupedRecord.bounded (fun size => KeyedSource.family program size key) bound).plan))).2
    (GroupedRecord.bounded_valid _ (fun size => KeyedSource.family_valid program size key) bound).1.2
    (by
      intro rank
      simp [Decoder.decode_correct, SamplerReplay.source, counting, Decoder.values,
        List.map_map, Function.comp_def])
    (unweighted_family_rankLaw program leaves key bound)
  simpa [Probability.map, RecursiveJoinRuntime.boundedSampler] using replay

end MicroCFTA.RecursiveUniformRuntime
