import MicroCFTA.FinalObservationRanks
import MicroCFTA.Sampler

/-!
# Retained masses through final observation merging

The outer mass of a bucket is separate from its conditional member masses.
Each source merge selects buckets by outer mass. The member rank interval uses
counts. Integer conversion preserves the normalized rational branch weights.
-/
namespace MicroCFTA.FinalObservationMass
open Language IntegerTermViews Probability

/-- Finite fields read by mergeBucketGroup and the final public ungroup. -/
structure Bucket (Symbol Value : Type) where
  index : FinalObservationRanks.Index Symbol
  mass : Rat
  conditional : Distribution Value

/-- Constructor-derived rank, count, and conditional probability invariants. -/
structure Valid (bucket : Bucket Symbol Value) : Prop where
  ranks : FinalObservationRanks.Exact bucket.index
  count : bucket.conditional.length = bucket.index.count
  probability : IsProbability bucket.conditional
  positive : 0 < bucket.mass

/-- Source branch records before rational-to-integer conversion. -/
def alternatives (buckets : List (Bucket Symbol Value)) : List (Rat × Distribution Value) :=
  buckets.map (fun bucket => (bucket.mass, bucket.conditional))

/-- The sum stored in the merged outer mass field. -/
def totalMass (buckets : List (Bucket Symbol Value)) : Rat := (buckets.map Bucket.mass).sum

/-- Expand every conditional member at its retained source bucket mass. -/
def raw (buckets : List (Bucket Symbol Value)) : Distribution Value :=
  buckets.flatMap (fun bucket => scale bucket.mass bucket.conditional)

theorem alternatives_weight (buckets : List (Bucket Symbol Value)) :
    branchWeight (alternatives buckets) = totalMass buckets := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih => simpa [alternatives, branchWeight, totalMass] using congrArg (bucket.mass + ·) ih

theorem alternatives_mix (buckets : List (Bucket Symbol Value)) :
    mix (alternatives buckets) = raw buckets := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih =>
      change scale bucket.mass bucket.conditional ++ mix (alternatives rest) =
        scale bucket.mass bucket.conditional ++ raw rest
      rw [ih]

/-- Source conversion changes only a common weight scale. -/
theorem integer_alternatives (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (positive : ∀ bucket ∈ buckets, 0 < bucket.mass) :
    normalize (Sampler.weightDistribution (Sampler.integerMasses (alternatives buckets))) =
      normalize (alternatives buckets) := by
  apply Sampler.integerMasses_normalize
  · simpa [alternatives] using nonempty
  · intro entry present
    obtain ⟨bucket, member, rfl⟩ := List.mem_map.mp present
    exact positive bucket member

/-- A frequency is the mixture of its normalized branch weights. -/
theorem frequency_normalized_weights (branches : List (Rat × Distribution Value)) :
    frequency branches = mix (normalize branches) := by
  have scale_mix : ∀ branches : List (Rat × Distribution Value), ∀ factor,
      mix (scale factor branches) = scale factor (mix branches) := by
    intro branches
    induction branches with
    | nil => intro factor; rfl
    | cons branch rest ih =>
        intro factor
        change scale (factor * branch.1) branch.2 ++ mix (scale factor rest) =
          scale factor (scale branch.1 branch.2 ++ mix rest)
        rw [ih]
        simp only [scale, List.map_append, List.map_map, Function.comp_def, Rat.mul_assoc]
  have same : total branches = branchWeight branches := by
    induction branches with
    | nil => rfl
    | cons branch rest ih => simp [total, branchWeight, ih]
  rw [normalize, scale_mix, same]
  rfl

/-- Actual integerOutcomes conversion preserves each branch's conditional law. -/
theorem integer_frequency (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (positive : ∀ bucket ∈ buckets, 0 < bucket.mass) :
    frequency (Sampler.weightDistribution (Sampler.integerMasses (alternatives buckets))) =
      frequency (alternatives buckets) := by
  rw [frequency_normalized_weights, frequency_normalized_weights, integer_alternatives buckets nonempty positive]

/-- The general source branch adds Choice terms and normalizes outer masses. -/
def merge (buckets : List (Bucket Symbol Value)) : Bucket Symbol Value :=
  match buckets with
  | [bucket] => bucket
  | _ => ⟨FinalObservationRanks.mergeIndex (buckets.map Bucket.index), totalMass buckets,
      frequency (alternatives buckets)⟩

/-- integerOutcomes rejects empty inputs and every nonpositive mass. -/
def checkedMerge (buckets : List (Bucket Symbol Value)) : Except Unit (Bucket Symbol Value) :=
  if buckets.isEmpty || buckets.any (fun bucket => decide (bucket.mass ≤ 0)) then .error ()
  else .ok (merge buckets)

/-- A source success is exactly the nonempty positive domain; errors are not empty languages. -/
theorem checkedMerge_exact (buckets : List (Bucket Symbol Value)) (result : Bucket Symbol Value) :
    checkedMerge buckets = .ok result ↔
      buckets ≠ [] ∧ (∀ bucket ∈ buckets, 0 < bucket.mass) ∧ result = merge buckets := by
  simp only [checkedMerge, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true, decide_eq_true_eq]
  split
  · rename_i rejected
    constructor
    · intro impossible; cases impossible
    · rintro ⟨nonempty, positive, _⟩
      rcases rejected with empty | ⟨bucket, member, bad⟩
      · exact False.elim (nonempty empty)
      · exact False.elim (Rat.not_lt.mpr bad (positive bucket member))
  · rename_i accepted
    simp only [Except.ok.injEq]
    constructor
    · intro same
      refine ⟨fun empty => accepted (Or.inl empty), ?_, same.symm⟩
      intro bucket member
      exact Rat.not_le.mp (fun bad => accepted (Or.inr ⟨bucket, member, bad⟩))
    · exact fun ⟨_, _, same⟩ => same.symm

theorem totalMass_positive (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (positive : ∀ bucket ∈ buckets, 0 < bucket.mass) : 0 < totalMass buckets := by
  have equal : total (buckets.map (fun bucket => (bucket.mass, ()))) = totalMass buckets := by
    clear nonempty positive
    induction buckets with
    | nil => rfl
    | cons bucket rest ih => simpa [total, totalMass] using congrArg (bucket.mass + ·) ih
  rw [← equal]
  apply Sized.total_positive
  · simpa using nonempty
  · intro entry present
    obtain ⟨bucket, member, rfl⟩ := List.mem_map.mp present
    exact positive bucket member

/-- Source size-mass adapters and inspection names do not alter these global fields. -/
theorem merge_index (buckets : List (Bucket Symbol Value)) :
    (merge buckets).index = FinalObservationRanks.mergeIndex (buckets.map Bucket.index) := by
  unfold merge
  split <;> rfl

theorem merge_mass (buckets : List (Bucket Symbol Value)) : (merge buckets).mass = totalMass buckets := by
  unfold merge
  split <;> simp [totalMass, Rat.add_zero]

theorem raw_count (buckets : List (Bucket Symbol Value))
    (counts : ∀ bucket ∈ buckets, bucket.conditional.length = bucket.index.count) :
    (raw buckets).length = FinalObservationRanks.totalCount (buckets.map Bucket.index) := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih =>
      change (scale bucket.mass bucket.conditional ++ raw rest).length = _
      simp only [List.length_append, scale, List.length_map]
      change bucket.conditional.length + (raw rest).length = _
      rw [counts bucket (by simp), ih (fun bucket member => counts bucket (by simp [member]))]
      rfl

/-- The conditional stream and the private term selector have the same count at every merge. -/
theorem merge_count (buckets : List (Bucket Symbol Value))
    (counts : ∀ bucket ∈ buckets, bucket.conditional.length = bucket.index.count) :
    (merge buckets).conditional.length = (merge buckets).index.count := by
  unfold merge
  split
  · exact counts _ (by simp)
  · simp only [frequency, scale, List.length_map, alternatives_mix, FinalObservationRanks.merge_count]
    exact raw_count _ counts

/-- A nonempty positive source merge reconstructs the unnormalized input stream exactly. -/
theorem merge_restore (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (positive : ∀ bucket ∈ buckets, 0 < bucket.mass) :
    scale (merge buckets).mass (merge buckets).conditional = raw buckets := by
  unfold merge
  split
  · simp [raw]
  · simp only [frequency, alternatives_weight, alternatives_mix, scale_scale]
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt (totalMass_positive buckets nonempty positive)), scale_one]

/-- All finite source-record invariants compose through a positive merge. -/
theorem merge_valid (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) : Valid (merge buckets) := by
  refine ⟨?_, merge_count buckets (fun bucket member => (valid bucket member).count), ?_, ?_⟩
  · rw [merge_index]
    apply FinalObservationRanks.merge_exact
    intro index present
    obtain ⟨bucket, member, rfl⟩ := List.mem_map.mp present
    exact (valid bucket member).ranks
  · unfold merge
    split
    · exact (valid _ (by simp)).probability
    · apply frequency_probability
      · intro entry present
        obtain ⟨bucket, member, rfl⟩ := List.mem_map.mp present
        exact ⟨Rat.le_of_lt (valid bucket member).positive, (valid bucket member).probability⟩
      · rw [alternatives_weight]
        exact totalMass_positive buckets nonempty (fun bucket member => (valid bucket member).positive)
  · rw [merge_mass]
    exact totalMass_positive buckets nonempty (fun bucket member => (valid bucket member).positive)

/-- The normalized conditional field uses the actual retained source mass. -/
theorem merge_conditional (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) :
    (merge buckets).conditional = normalize (raw buckets) := by
  rw [← merge_restore buckets nonempty (fun bucket member => (valid bucket member).positive)]
  rw [normalize_scale _ _ (Rat.ne_of_gt (merge_valid buckets nonempty valid).positive)]
  simp [normalize, (merge_valid buckets nonempty valid).probability.2, scale_one]

/-- Actual finite regroupOn partitions buckets before it merges them. -/
def regroup [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : List (Bucket Symbol Value) :=
  (GeneratorCombinators.groupOutcomes before key buckets).map merge

theorem regroup_valid [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (valid : ∀ bucket ∈ buckets, Valid bucket)
    (result : Bucket Symbol Value) (present : result ∈ regroup before key buckets) : Valid result := by
  obtain ⟨group, member, rfl⟩ := List.mem_map.mp present
  have shape := GeneratorCombinators.groupOutcomes_key before key buckets group member
  apply merge_valid group
  · obtain ⟨first, rest, rfl, _⟩ := shape; simp
  · intro bucket present
    exact valid bucket ((GeneratorCombinators.groupOutcomes_perm before key buckets).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, member, present⟩))

/-- Observation regrouping retains every weighted input occurrence, up to map order. -/
theorem regroup_raw [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (positive : ∀ bucket ∈ buckets, 0 < bucket.mass) :
    (raw (regroup before key buckets)).Perm (raw buckets) := by
  have expanded : raw (regroup before key buckets) =
      (GeneratorCombinators.groupOutcomes before key buckets).flatMap raw := by
    simp only [raw, regroup, List.flatMap_map]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro group member
    obtain ⟨first, rest, same, _⟩ := GeneratorCombinators.groupOutcomes_key before key buckets group member
    exact merge_restore group (by simp [same]) (fun bucket present => positive bucket
      ((GeneratorCombinators.groupOutcomes_perm before key buckets).mem_iff.mp
        (List.mem_flatten.mpr ⟨group, member, present⟩)))
  rw [expanded]
  have flattenRaw : ∀ groups : List (List (Bucket Symbol Value)),
      groups.flatMap raw = raw groups.flatten := by
    intro groups
    induction groups with
    | nil => rfl
    | cons group rest ih =>
        change raw group ++ rest.flatMap raw = raw (group ++ rest.flatten)
        rw [ih]
        simp only [raw, List.flatMap_append]
  rw [flattenRaw]
  exact (GeneratorCombinators.groupOutcomes_perm before key buckets).flatMap_right
    (fun bucket => scale bucket.mass bucket.conditional)

/-- The final source ungroup preserves the conditioned input law under any observation partition. -/
theorem final_distribution [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) (event : Value → Bool) :
    eventMass event (merge (regroup before key buckets)).conditional =
      eventMass event (normalize (raw buckets)) := by
  have groupedNonempty : regroup before key buckets ≠ [] := by
    intro empty
    have groupsEmpty : GeneratorCombinators.groupOutcomes before key buckets = [] := by
      simpa [regroup] using empty
    have permutation := GeneratorCombinators.groupOutcomes_perm before key buckets
    rw [groupsEmpty] at permutation
    exact nonempty (List.Perm.nil_eq permutation).symm
  rw [merge_conditional _ groupedNonempty (regroup_valid before key buckets valid)]
  exact normalized_perm_event event (regroup_raw before key buckets (fun bucket member => (valid bucket member).positive))


/-- A retained integer source keeps branch provenance, original rank, and its decoded tuple. -/
def settledBucket (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (closed : OpenGroupedApplication.ClosedBucket Value) :
    Bucket IntegerLabelCodec.Symbol (Nat × Nat × List Int) :=
  ⟨FinalObservationRanks.pointIndex IntegerLabelCodec.integerSymbol specialize IntegerLabelCodec.leafValue
      symbol (IntegerLabelCodec.fills symbol) closed.original.source closed.points,
    closed.original.mass * closed.kept,
    Probability.map (fun entry => (origin, entry))
      (Probability.product (OpenGroupedApplication.rankDistribution closed.original.source)
        (Probability.normalize (Probability.counting (OpenIntegerSource.pointDomain closed.points))))⟩

/-- The settlement seed uses the same outer mass and complete original/point law as the compiled record. -/
theorem settledBucket_raw (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (closed : OpenGroupedApplication.ClosedBucket Value) :
    raw [settledBucket origin specialize symbol closed] =
      Probability.map (fun entry => (origin, entry)) (OpenGroupedApplication.closedDistribution closed) := by
  simp only [raw, List.flatMap_cons, List.flatMap_nil, List.append_nil, settledBucket,
    OpenGroupedApplication.closedDistribution, scale, Probability.map, List.map_map, Function.comp_def]

/-- Every successful retained table has a strictly positive natural point count. -/
theorem settled_points_positive (parents : List FullSyntax.Formula)
    (bucket : OpenGroupedApplication.Bucket Value) (closed : OpenGroupedApplication.ClosedBucket Value)
    (success : OpenGroupedApplication.settle parents bucket = .ok (some closed)) :
    0 < closed.points.count.toNat := by
  have fields := OpenGroupedApplication.settle_fields parents bucket closed success
  have nonnegative := (LatticeAPI.points_count _ _ _ fields.2.2.1).2
  omega

/-- Actual finite child tables and the successful parent table derive every seed-record invariant. -/
theorem settledBucket_valid (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (parents : List FullSyntax.Formula) (bucket : OpenGroupedApplication.Bucket Value)
    (closed : OpenGroupedApplication.ClosedBucket Value)
    (success : OpenGroupedApplication.settle parents bucket = .ok (some closed))
    (sourceMass : OpenGroupedApplication.ValidMass bucket.source) (outerPositive : 0 < bucket.mass)
    (tables : OpenIntegerKeys.Key → LatticeAPI.Points)
    (built : ∀ key ∈ (OpenGroupedApplication.keys bucket.source).map OpenGroupComposition.openKey,
      LatticeAPI.points (OpenIntegerKeys.names key.width) (FullSyntax.lowerFormula key.formula) = .ok (tables key))
    (stored : ∀ key ∈ (OpenGroupedApplication.keys bucket.source).map OpenGroupComposition.openKey,
      key.points = some (tables key).count.toNat) :
    Valid (settledBucket origin specialize symbol closed) := by
  have fields := OpenGroupedApplication.settle_fields parents bucket closed success
  have pointPositive := settled_points_positive parents bucket closed success
  have exactTable := LatticeSelect.points_api_exact _ _ _ fields.2.2.1
  have domainSize := OpenIntegerSource.pointDomain_count _ _ closed.points fields.2.2.1
  constructor
  · simp only [settledBucket, fields.1]
    exact FinalObservationRanks.settledIndex_exact specialize symbol specialized parents bucket closed success
  · simp only [settledBucket, Probability.map, List.length_map, SizeMass.product_length,
      Probability.normalize, Probability.scale, Probability.counting, OpenGroupedApplication.rankDistribution_count,
      FinalObservationRanks.pointIndex]
    rw [domainSize, exactTable.1]
  · simp only [settledBucket, fields.1]
    apply OpenGroupedApplication.map_probability
    apply Probability.product_probability
    · exact OpenGroupedApplication.rankDistribution_probability bucket.source sourceMass
    · exact Probability.uniform_probability _ (by simpa [domainSize] using pointPositive)
  · change 0 < closed.original.mass * closed.kept
    rw [fields.1, fields.2.2.2]
    apply Rat.mul_pos outerPositive
    rw [RecipeCompile.retainedShare, Rat.div_def]
    apply Rat.mul_pos (Rat.natCast_pos.mpr pointPositive)
    apply Rat.inv_pos.mpr
    apply Rat.natCast_pos.mpr
    apply ParentIntegerSettlement.retained_denominator_positive
      ((OpenGroupedApplication.keys bucket.source).map OpenGroupComposition.openKey) parents
      (fun key member => LatticeDeclaredNames.points_scoped _ _ _ (built key member))
      (fun key => OpenIntegerSource.pointDomain (tables key))
      (fun key member tuple => OpenIntegerSource.pointDomain_exact _ _ _ (built key member) tuple)
      (fun key member => OpenIntegerSource.pointDomain_distinct _ _ _ (built key member))
      (fun key member => by rw [OpenIntegerSource.pointDomain_count _ _ _ (built key member)]; exact stored key member)
      closed.points
    · simpa [OpenGroupedApplication.parentFormula, OpenGroupedApplication.width, OpenIntegerKeys.join,
        List.map_map, OpenGroupComposition.openKey, Function.comp_def] using fields.2.2.1
    · exact pointPositive

/-- The final global count is the sum of the incoming original-times-point counts. -/
theorem final_count [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) :
    (merge (regroup before key buckets)).index.count =
      FinalObservationRanks.totalCount (buckets.map Bucket.index) := by
  have groupedNonempty : regroup before key buckets ≠ [] := by
    intro empty
    have groupsEmpty : GeneratorCombinators.groupOutcomes before key buckets = [] := by
      simpa [regroup] using empty
    have permutation := GeneratorCombinators.groupOutcomes_perm before key buckets
    rw [groupsEmpty] at permutation
    exact nonempty (List.Perm.nil_eq permutation).symm
  have merged := merge_valid _ groupedNonempty (regroup_valid before key buckets valid)
  rw [← merged.count]
  have restored := congrArg List.length (merge_restore (regroup before key buckets) groupedNonempty
    (fun bucket member => (regroup_valid before key buckets valid bucket member).positive))
  simp only [scale, List.length_map] at restored
  rw [restored, (regroup_raw before key buckets (fun bucket member => (valid bucket member).positive)).length_eq]
  exact raw_count buckets (fun bucket member => (valid bucket member).count)

/-- Checked bucket traversal cannot turn an invalid mass into an empty successful group. -/
def checkedRegroup [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : Except Unit (List (Bucket Symbol Value)) :=
  (GeneratorCombinators.groupOutcomes before key buckets).mapM checkedMerge

/-- Every constructor-valid finite group passes the actual merge error gate. -/
theorem checkedRegroup_success [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (valid : ∀ bucket ∈ buckets, Valid bucket) :
    checkedRegroup before key buckets = .ok (regroup before key buckets) := by
  have each : ∀ group ∈ GeneratorCombinators.groupOutcomes before key buckets,
      checkedMerge group = .ok (merge group) := by
    intro group member
    obtain ⟨first, rest, same, _⟩ := GeneratorCombinators.groupOutcomes_key before key buckets group member
    apply (checkedMerge_exact group _).mpr
    refine ⟨by simp [same], ?_, rfl⟩
    intro bucket present
    exact (valid bucket ((GeneratorCombinators.groupOutcomes_perm before key buckets).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, member, present⟩))).positive
  unfold checkedRegroup regroup
  generalize groupsEq : GeneratorCombinators.groupOutcomes before key buckets = groups at *
  clear groupsEq
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.mapM_cons, each group (by simp), List.map_cons]
      have later := ih (fun group member => each group (by simp [member]))
      rw [later]
      rfl


/-- mergeComponentsByKey divides every outer mass by the same accepted total. -/
def normalizeBuckets (buckets : List (Bucket Symbol Value)) : List (Bucket Symbol Value) :=
  buckets.map (fun bucket => { bucket with mass := bucket.mass / totalMass buckets })

/-- Outer normalization does not change any rank record or conditional member distribution. -/
theorem normalize_fields (buckets : List (Bucket Symbol Value)) :
    (normalizeBuckets buckets).map (fun bucket => (bucket.index, bucket.conditional)) =
      buckets.map (fun bucket => (bucket.index, bucket.conditional)) := by
  simp [normalizeBuckets, List.map_map]

/-- The normalized outer fields apply one common scale to the complete source stream. -/
theorem normalize_raw (buckets : List (Bucket Symbol Value)) :
    raw (normalizeBuckets buckets) = scale (totalMass buckets)⁻¹ (raw buckets) := by
  simp only [normalizeBuckets, raw, List.flatMap_map]
  have scale_flatMap : ∀ parts : List (Bucket Symbol Value), ∀ factor,
      parts.flatMap (fun bucket => scale (bucket.mass * factor) bucket.conditional) =
        scale factor (parts.flatMap (fun bucket => scale bucket.mass bucket.conditional)) := by
    intro parts
    induction parts with
    | nil => intro factor; rfl
    | cons bucket rest ih =>
        intro factor
        simp only [List.flatMap_cons]
        rw [ih]
        simp only [scale, List.map_append, List.map_map, Function.comp_def]
        congr 2
        funext entry
        congr 1
        rw [Rat.mul_comm bucket.mass factor, Rat.mul_assoc]
  simpa only [Rat.div_def] using scale_flatMap buckets (totalMass buckets)⁻¹

/-- Constructor-valid records stay valid after source outer-mass normalization. -/
theorem normalize_valid (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) (result : Bucket Symbol Value)
    (present : result ∈ normalizeBuckets buckets) : Valid result := by
  obtain ⟨bucket, member, rfl⟩ := List.mem_map.mp present
  have original := valid bucket member
  refine ⟨original.ranks, original.count, original.probability, ?_⟩
  change 0 < bucket.mass / totalMass buckets
  rw [Rat.div_def]
  exact Rat.mul_pos original.positive (Rat.inv_pos.mpr
    (totalMass_positive buckets nonempty (fun bucket member => (valid bucket member).positive)))

/-- Source result-key grouping is followed by accepted-mass normalization. -/
def resultGroups [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : List (Bucket Symbol Value) :=
  normalizeBuckets (regroup before key buckets)

/-- A nonempty source family has a nonempty observation result map. -/
theorem regroup_nonempty [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ []) : regroup before key buckets ≠ [] := by
  intro empty
  have groupsEmpty : GeneratorCombinators.groupOutcomes before key buckets = [] := by
    simpa [regroup] using empty
  have permutation := GeneratorCombinators.groupOutcomes_perm before key buckets
  rw [groupsEmpty] at permutation
  exact nonempty (List.Perm.nil_eq permutation).symm

/-- The complete final finite compiler merge has exact ranks and a normalized law. -/
theorem result_valid [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) : Valid (merge (resultGroups before key buckets)) := by
  apply merge_valid
  · simpa [resultGroups, normalizeBuckets] using regroup_nonempty before key buckets nonempty
  · exact normalize_valid _ (regroup_nonempty before key buckets nonempty) (regroup_valid before key buckets valid)

/-- The source's extra accepted-mass normalization cannot change final member probabilities. -/
theorem result_distribution [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) (event : Value → Bool) :
    eventMass event (merge (resultGroups before key buckets)).conditional =
      eventMass event (normalize (raw buckets)) := by
  have groupedNonempty := regroup_nonempty before key buckets nonempty
  have groupedValid := regroup_valid before key buckets valid
  have normalizedNonempty : resultGroups before key buckets ≠ [] := by
    simpa [resultGroups, normalizeBuckets] using groupedNonempty
  rw [merge_conditional _ normalizedNonempty (normalize_valid _ groupedNonempty groupedValid)]
  rw [resultGroups, normalize_raw, normalize_scale _ _
    (Rat.ne_of_gt (Rat.inv_pos.mpr (totalMass_positive _ groupedNonempty
      (fun bucket member => (groupedValid bucket member).positive))))]
  exact normalized_perm_event event (regroup_raw before key buckets (fun bucket member => (valid bucket member).positive))

/-- The final accepted-mass normalization leaves the sum of compiled member counts unchanged. -/
theorem result_count [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) :
    (merge (resultGroups before key buckets)).index.count =
      (merge (regroup before key buckets)).index.count := by
  rw [merge_index, merge_index, FinalObservationRanks.merge_count, FinalObservationRanks.merge_count]
  simp [resultGroups, normalizeBuckets, List.map_map, Function.comp_def]

/-- Every final rank is a member position; view queries return all and only its replay preimages. -/
theorem result_ranks [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) (view : View)
    (wanted : List (Term (GeneratorCombinators.Label Symbol))) (rank : Nat) :
    rank ∈ (merge (resultGroups before key buckets)).index.ranks view wanted ↔
      ∃ term, (merge (resultGroups before key buckets)).index.select rank = some term ∧
        project view term = wanted :=
  (result_valid before key buckets nonempty valid).ranks.ranks view wanted rank

/-- There are no missing or extra indices in the final finite compiler result. -/
theorem result_interval [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) (rank : Nat) :
    (∃ term, (merge (resultGroups before key buckets)).index.select rank = some term) ↔
      rank < FinalObservationRanks.totalCount (buckets.map Bucket.index) := by
  rw [(result_valid before key buckets nonempty valid).ranks.bounds,
    result_count, final_count before key buckets nonempty valid]


/-- The expanded stream uses the same prefix cardinality as the term selector. -/
theorem raw_rank (before after : List (Bucket Symbol Value)) (bucket : Bucket Symbol Value)
    (counts : ∀ entry ∈ before, entry.conditional.length = entry.index.count)
    (rank : Nat) (weight : Rat) (value : Value)
    (found : bucket.conditional[rank]? = some (weight, value)) :
    (raw (before ++ bucket :: after))[FinalObservationRanks.totalCount (before.map Bucket.index) + rank]? =
      some (bucket.mass * weight, value) := by
  have inside : rank < bucket.conditional.length := List.getElem?_eq_some_iff.mp found |>.1
  rw [show raw (before ++ bucket :: after) = raw before ++ (scale bucket.mass bucket.conditional ++ raw after) by
    simp only [raw, List.flatMap_append, List.flatMap_cons]]
  rw [List.getElem?_append_right (l₁ := raw before) (by rw [raw_count before counts]; omega), raw_count before counts]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [scale] using inside), scale, List.getElem?_map, found]
  rfl

/-- A non-singleton source merge uses external bucket mass and retains each child member mass. -/
theorem merged_rank_mass (before after : List (Bucket Symbol Value)) (bucket : Bucket Symbol Value)
    (many : ¬(before = [] ∧ after = []))
    (counts : ∀ entry ∈ before, entry.conditional.length = entry.index.count)
    (rank : Nat) (weight : Rat) (value : Value)
    (found : bucket.conditional[rank]? = some (weight, value)) :
    (merge (before ++ bucket :: after)).conditional[FinalObservationRanks.totalCount (before.map Bucket.index) + rank]? =
      some (bucket.mass / totalMass (before ++ bucket :: after) * weight, value) := by
  have notSingleton : ∀ only, before ++ bucket :: after ≠ [only] := by
    intro only same
    have length := congrArg List.length same
    have left : before = [] := List.length_eq_zero_iff.mp (by simp at length; omega)
    have right : after = [] := List.length_eq_zero_iff.mp (by simp at length; omega)
    exact many ⟨left, right⟩
  simp only [merge]
  change (frequency (alternatives (before ++ bucket :: after)))[FinalObservationRanks.totalCount (before.map Bucket.index) + rank]? = _
  rw [frequency, alternatives_weight, alternatives_mix, scale, List.getElem?_map,
    raw_rank before after bucket counts rank weight value found]
  simp only [Option.map_some, Rat.div_def]
  rw [← Rat.mul_assoc, Rat.mul_comm _ bucket.mass]

/-- The private term and the conditional member mass use one shared rank offset. -/
theorem merged_rank_record (before after : List (Bucket Symbol Value)) (bucket : Bucket Symbol Value)
    (many : ¬(before = [] ∧ after = []))
    (counts : ∀ entry ∈ before, entry.conditional.length = entry.index.count)
    (rank : Nat) (weight : Rat) (value : Value) (term : Term (GeneratorCombinators.Label Symbol))
    (inside : rank < bucket.index.count) (selected : bucket.index.select rank = some term)
    (found : bucket.conditional[rank]? = some (weight, value)) :
    let offset := FinalObservationRanks.totalCount (before.map Bucket.index)
    (merge (before ++ bucket :: after)).index.select (offset + rank) =
      some (.node (.choice before.length) [term]) ∧
    (merge (before ++ bucket :: after)).conditional[offset + rank]? =
      some (bucket.mass / totalMass (before ++ bucket :: after) * weight, value) := by
  dsimp only
  refine ⟨?_, merged_rank_mass before after bucket many counts rank weight value found⟩
  rw [merge_index]
  simp only [List.map_append, List.map_cons]
  have replay := FinalObservationRanks.mergeIndex_member (before.map Bucket.index) (after.map Bucket.index)
    bucket.index rank term inside selected
  simpa [many] using replay


/-- Final result-key merge and unit-key ungroup keep the source EmptyGenerator boundary. -/
def checkedResult [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : Except Unit (Bucket Symbol Value) := do
  if buckets.isEmpty then .error () else do
    let groups ← checkedRegroup before key buckets
    checkedMerge (normalizeBuckets groups)

/-- A successful finite family reaches the concrete final rank and distribution record. -/
theorem checkedResult_success [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, Valid bucket) :
    checkedResult before key buckets = .ok (merge (resultGroups before key buckets)) := by
  have groupsNonempty := regroup_nonempty before key buckets nonempty
  have normalizedNonempty : normalizeBuckets (regroup before key buckets) ≠ [] := by
    simpa [normalizeBuckets] using groupsNonempty
  have normalizedValid := normalize_valid _ groupsNonempty (regroup_valid before key buckets valid)
  have merged := (checkedMerge_exact (normalizeBuckets (regroup before key buckets)) _).mpr
    ⟨normalizedNonempty, fun bucket member => (normalizedValid bucket member).positive, rfl⟩
  simp only [checkedResult, List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true,
    ↓reduceIte, checkedRegroup_success before key buckets valid]
  exact merged

/-- Source EmptyGenerator remains an error even though the reference zero-count index is total. -/
theorem checkedResult_empty [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key) :
    checkedResult before key [] = .error () := rfl

end MicroCFTA.FinalObservationMass




