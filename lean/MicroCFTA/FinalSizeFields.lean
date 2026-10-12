import MicroCFTA.OpenGroupedSize

/-!
# Final finite bucket size fields

The regular merge uses class counts or retained class masses. The source's
same-size atomic merge instead takes its size distribution from the merged
global outcomes. Both paths keep the same original member rank interval.
-/
namespace MicroCFTA.FinalSizeFields
open Probability SourcePlanPositions FiniteSizeFields

/-- Couple the source global fields with their independently constructed size fields. -/
structure Bucket (Symbol Value : Type) where
  global : FinalObservationMass.Bucket Symbol Value
  sizes : Record

/-- Alignment concerns the actual shared member interval, not an assumed decoder inverse. -/
structure Aligned (bucket : Bucket Symbol Value) : Prop where
  sizes : Valid bucket.sizes
  count : count bucket.sizes.plan = bucket.global.index.count

/-- Construct size fields for an actual successful integer settlement. -/
def settled (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (record : OpenGroupedApplication.ClosedBucket Value) :
    Bucket IntegerLabelCodec.Symbol (Nat × Nat × List Int) :=
  ⟨FinalObservationMass.settledBucket origin specialize symbol record,
    OpenGroupedSize.closed record.original.source (LatticeSelect.pointCount record.points.levels)⟩

/-- The original grouped constructors derive count and size alignment for each settlement. -/
theorem settled_aligned (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (record : OpenGroupedApplication.ClosedBucket Value) :
    Aligned (settled origin specialize symbol record) :=
  ⟨OpenGroupedSize.closed_valid _ _, OpenGroupedSize.settled_count origin specialize symbol record⟩

/-- Source frequency construction for a non-atomic merge, or a merge with retained masses. -/
def regularMerge (buckets : List (Bucket Symbol Value)) : Bucket Symbol Value :=
  ⟨FinalObservationMass.merge (buckets.map Bucket.global), OpenGroupedSize.merge (buckets.map Bucket.sizes)⟩

/-- Nested frequency wrappers use one count interval in both global and size records. -/
theorem regularMerge_aligned (buckets : List (Bucket Symbol Value))
    (aligned : ∀ bucket ∈ buckets, Aligned bucket) : Aligned (regularMerge buckets) := by
  constructor
  · apply OpenGroupedSize.merge_valid
    intro record member
    obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
    exact (aligned bucket present).sizes
  · change count (OpenGroupedSize.merge _).plan = (FinalObservationMass.merge _).index.count
    rw [OpenGroupedSize.merge_count, FinalObservationMass.merge_index, FinalObservationRanks.merge_count]
    simp only [FinalObservationRanks.totalCount, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro bucket member
    exact (aligned bucket member).count

/-- Partition and merge the final observation buckets in source key order. -/
def regroup [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : List (Bucket Symbol Value) :=
  (GeneratorCombinators.groupOutcomes before key buckets).map regularMerge

theorem regroup_aligned [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (aligned : ∀ bucket ∈ buckets, Aligned bucket)
    (result : Bucket Symbol Value) (member : result ∈ regroup before key buckets) : Aligned result := by
  obtain ⟨group, grouped, rfl⟩ := List.mem_map.mp member
  apply regularMerge_aligned
  intro bucket present
  exact aligned bucket ((GeneratorCombinators.groupOutcomes_perm before key buckets).mem_iff.mp
    (List.mem_flatten.mpr ⟨group, grouped, present⟩))

/-- Global accepted-mass normalization does not alter size fields or member ranks. -/
def normalize (buckets : List (Bucket Symbol Value)) : List (Bucket Symbol Value) :=
  buckets.map fun bucket => { bucket with global := { bucket.global with
    mass := bucket.global.mass / FinalObservationMass.totalMass (buckets.map Bucket.global) } }

theorem normalize_aligned (buckets : List (Bucket Symbol Value))
    (aligned : ∀ bucket ∈ buckets, Aligned bucket) (result : Bucket Symbol Value)
    (member : result ∈ normalize buckets) : Aligned result := by
  obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
  exact ⟨(aligned bucket present).sizes, (aligned bucket present).count⟩

/-- Final result-key normalization and unit-key ungroup construct one aligned finite record. -/
def result [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) : Bucket Symbol Value :=
  regularMerge (normalize (regroup before key buckets))

theorem result_aligned [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (aligned : ∀ bucket ∈ buckets, Aligned bucket) :
    Aligned (result before key buckets) :=
  regularMerge_aligned _ (normalize_aligned _ (regroup_aligned before key buckets aligned))

/-- The actual retainAtomic path rebuilds one fixed-size class from the merged global law. -/
def atomicMerge (size : Nat) (buckets : List (Bucket Symbol Value)) : Bucket Symbol Value :=
  let global := FinalObservationMass.merge (buckets.map Bucket.global)
  ⟨global, atomic size global.conditional⟩


/-- Positive child outcomes stay positive through source integer weighting and conditional merging. -/
theorem merge_positive (buckets : List (FinalObservationMass.Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (outer : ∀ bucket ∈ buckets, 0 < bucket.mass)
    (inner : ∀ bucket ∈ buckets, ∀ entry ∈ bucket.conditional, 0 < entry.1) :
    ∀ entry ∈ (FinalObservationMass.merge buckets).conditional, 0 < entry.1 := by
  unfold FinalObservationMass.merge
  split
  · exact inner _ (by simp)
  · intro entry member
    have totalPositive := FinalObservationMass.totalMass_positive buckets nonempty outer
    change entry ∈ Probability.frequency (FinalObservationMass.alternatives buckets) at member
    rw [Probability.frequency, FinalObservationMass.alternatives_weight, FinalObservationMass.alternatives_mix] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨bucket, bucketMember, member⟩ := List.mem_flatMap.mp present
    obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
    cases same
    exact Rat.mul_pos (Rat.inv_pos.mpr totalPositive)
      (Rat.mul_pos (outer bucket bucketMember) (inner bucket bucketMember child childMember))

/-- Global constructor validity and positive declared masses derive the atomic merge fields. -/
theorem atomicMerge_aligned (size : Nat) (buckets : List (Bucket Symbol Value))
    (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global)
    (positive : ∀ bucket ∈ buckets, ∀ entry ∈ bucket.global.conditional, 0 < entry.1) :
    Aligned (atomicMerge size buckets) := by
  have merged := FinalObservationMass.merge_valid (buckets.map Bucket.global) (by simpa using nonempty) (by
    intro global member
    obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
    exact valid bucket present)
  have outputPositive := merge_positive (buckets.map Bucket.global) (by simpa using nonempty)
    (by
      intro global member
      obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
      exact (valid bucket present).positive)
    (by
      intro global member
      obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
      exact positive bucket present)
  refine ⟨atomic_valid size _ merged.probability outputPositive, ?_⟩
  change count (fixedPlan size _ ) = _
  rw [fixedPlan_count]
  exact merged.count

/-- The atomic branch uses the global conditional law, not ordinary count-weighted alternative choice. -/
theorem atomicMerge_probability (size : Nat) (buckets : List (Bucket Symbol Value))
    (live : (FinalObservationMass.merge (buckets.map Bucket.global)).conditional ≠ []) :
    FiniteSizeSampling.sample (atomicMerge size buckets).sizes size =
      rankedMasses (FinalObservationMass.merge (buckets.map Bucket.global)).conditional :=
  atomic_probability size _ live

/-- Per-size inverse lookup and global replay remain aligned after final regular observation merging. -/
theorem result_class_replay [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (part : SizedRank.Position) (rank : Nat)
    (converted : position (result before key buckets).sizes.plan rank = some part) :
    OpenGroupedSize.selectClass (result before key buckets).global.index (result before key buckets).sizes part.size part.rank =
      (result before key buckets).global.index.select rank :=
  OpenGroupedSize.selectClass_replay _ _ part rank converted


/-- The regular size-field adapter retains the already constructed complete global record. -/
theorem regularMerge_global (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global) :
    FinalObservationMass.Valid (regularMerge buckets).global := by
  apply FinalObservationMass.merge_valid
  · simpa using nonempty
  · intro global member
    obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
    exact valid bucket present

theorem regroup_global [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (valid : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global)
    (bucket : Bucket Symbol Value) (member : bucket ∈ regroup before key buckets) :
    FinalObservationMass.Valid bucket.global := by
  obtain ⟨group, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨first, rest, same, _⟩ := GeneratorCombinators.groupOutcomes_key before key buckets group present
  apply regularMerge_global group (by simp [same])
  intro bucket member
  exact valid bucket ((GeneratorCombinators.groupOutcomes_perm before key buckets).mem_iff.mp
    (List.mem_flatten.mpr ⟨group, present, member⟩))

theorem normalize_global (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global)
    (result : Bucket Symbol Value) (member : result ∈ normalize buckets) : FinalObservationMass.Valid result.global := by
  obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
  apply FinalObservationMass.normalize_valid (buckets.map Bucket.global) (by simpa using nonempty)
  · intro global member
    obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
    exact valid bucket present
  · exact List.mem_map.mpr ⟨bucket.global, List.mem_map.mpr ⟨bucket, present, rfl⟩, rfl⟩

theorem regroup_nonempty [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ []) : regroup before key buckets ≠ [] := by
  intro empty
  have noGroups : GeneratorCombinators.groupOutcomes before key buckets = [] := by simpa [regroup] using empty
  have permutation := GeneratorCombinators.groupOutcomes_perm before key buckets
  rw [noGroups] at permutation
  exact nonempty (List.Perm.nil_eq permutation).symm

theorem result_global [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (valid : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global) :
    FinalObservationMass.Valid (result before key buckets).global := by
  apply regularMerge_global
  · simpa [normalize] using regroup_nonempty before key buckets nonempty
  · exact normalize_global _ (regroup_nonempty before key buckets nonempty) (regroup_global before key buckets valid)

/-- All final size classes decode exactly their counted member interval after observation merges. -/
theorem result_class_decoder [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (nonempty : buckets ≠ [])
    (global : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.global)
    (aligned : ∀ bucket ∈ buckets, Aligned bucket) (size rank : Nat) :
    (∃ term, OpenGroupedSize.selectClass (result before key buckets).global.index
      (result before key buckets).sizes size rank = some term) ↔
      rank < (classRanks (result before key buckets).sizes.plan size).length :=
  OpenGroupedSize.selectClass_exists _ (result_global before key buckets nonempty global).ranks _
    (result_aligned before key buckets aligned).count size rank

/-- The same final class fields supply a normalized sampler at every live size. -/
theorem result_class_probability [DecidableEq Key] (before : Key → Key → Bool) (key : Bucket Symbol Value → Key)
    (buckets : List (Bucket Symbol Value)) (aligned : ∀ bucket ∈ buckets, Aligned bucket) (size : Nat)
    (nonempty : classRanks (result before key buckets).sizes.plan size ≠ []) :
    IsProbability (FiniteSizeSampling.sample (result before key buckets).sizes size) :=
  FiniteSizeSampling.sample_probability _ (result_aligned before key buckets aligned).sizes size nonempty

end MicroCFTA.FinalSizeFields

