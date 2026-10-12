import MicroCFTA.StaticSamplingDispatch

/-!
# Complete finite bucket merge branch selection

A positive singleton is returned directly. A larger merge uses retained
class masses before it considers atomic flags. A common-size atomic merge
uses the global conditional law. Every remaining merge uses class counts.
-/
namespace MicroCFTA.BucketMergeDispatch
open Probability SourcePlanPositions FiniteSizeFields

/-- Source bucket fields used by the merge guards. -/
structure Input (Symbol Value : Type) where
  data : FinalSizeFields.Bucket Symbol Value
  atomic : Bool
  minimum : Option Nat

/-- The source branch after the mass checks succeed. -/
inductive Mode where
  | singleton | retained | atomic (size : Nat) | ordinary
  deriving DecidableEq, Repr

/-- Retained masses have priority over atomic markers. -/
def hasMasses (buckets : List (Input Symbol Value)) : Bool :=
  buckets.any (fun bucket => bucket.data.sizes.retained.isSome)

/-- Match a nonempty list of atoms whose finite minimum sizes are equal. -/
def commonAtomicSize : List (Input Symbol Value) → Option Nat
  | [] => none
  | first :: rest =>
      match first.minimum with
      | none => none
      | some size =>
          if (first :: rest).all (fun bucket => bucket.atomic && decide (bucket.minimum = some size))
          then some size else none

/-- Execute every source merge guard in its original order. -/
def mode (buckets : List (Input Symbol Value)) : Mode :=
  match buckets with
  | [_] => .singleton
  | _ => if hasMasses buckets then .retained else
      match commonAtomicSize buckets with
      | some size => .atomic size
      | none => .ordinary

/-- The source field construction selected by the guards. -/
def merge (buckets : List (Input Symbol Value)) : FinalSizeFields.Bucket Symbol Value :=
  match buckets with
  | [bucket] => bucket.data
  | _ =>
      if hasMasses buckets then FinalSizeFields.regularMerge (buckets.map Input.data)
      else match commonAtomicSize buckets with
        | some size => FinalSizeFields.atomicMerge size (buckets.map Input.data)
        | none => FinalSizeFields.regularMerge (buckets.map Input.data)

/-- Frequency clears the marker. The atomic branch restores it. -/
def mergedAtomic (buckets : List (Input Symbol Value)) : Bool :=
  match buckets with
  | [bucket] => bucket.atomic
  | _ => !hasMasses buckets && (commonAtomicSize buckets).isSome

/-- integerOutcomes rejects empty inputs and every nonpositive bucket mass. -/
def checked (buckets : List (Input Symbol Value)) : Except Unit (FinalSizeFields.Bucket Symbol Value) :=
  if buckets.isEmpty || buckets.any (fun bucket => decide (bucket.data.global.mass ≤ 0))
  then .error () else .ok (merge buckets)

/-- A successful source merge has exactly the nonempty positive input domain. -/
theorem checked_exact (buckets : List (Input Symbol Value)) (result : FinalSizeFields.Bucket Symbol Value) :
    checked buckets = .ok result ↔ buckets ≠ [] ∧
      (∀ bucket ∈ buckets, 0 < bucket.data.global.mass) ∧ result = merge buckets := by
  simp only [checked, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true, decide_eq_true_eq]
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

/-- The singleton fast path preserves every source field, including retained tables. -/
theorem singleton (bucket : Input Symbol Value) (positive : 0 < bucket.data.global.mass) :
    checked [bucket] = .ok bucket.data ∧ mode [bucket] = .singleton ∧
      mergedAtomic [bucket] = bucket.atomic := by
  simp [checked, Rat.not_le.mpr positive, merge, mode, mergedAtomic]

/-- The atomic guard succeeds exactly when every marker and every minimum agrees. -/
theorem commonAtomicSize_exact (buckets : List (Input Symbol Value)) (size : Nat) :
    commonAtomicSize buckets = some size ↔ buckets ≠ [] ∧
      ∀ bucket ∈ buckets, bucket.atomic = true ∧ bucket.minimum = some size := by
  cases buckets with
  | nil => simp [commonAtomicSize]
  | cons first rest =>
      cases minimum : first.minimum with
      | none =>
          simp only [commonAtomicSize, minimum]
          constructor
          · intro impossible; cases impossible
          · intro all
            have := (all.2 first (by simp)).2
            simp [minimum] at this
      | some firstSize =>
          simp only [commonAtomicSize, minimum]
          split
          · rename_i every
            have all : ∀ bucket ∈ first :: rest,
                bucket.atomic = true ∧ bucket.minimum = some firstSize := by
              simpa only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using every
            constructor
            · intro same
              cases Option.some.inj same
              exact ⟨by simp, all⟩
            · intro wanted
              have same := (wanted.2 first (by simp)).2
              rw [minimum] at same
              exact same
          · rename_i notAll
            constructor
            · intro impossible; cases impossible
            · intro wanted
              have same := (wanted.2 first (by simp)).2
              rw [minimum] at same
              cases Option.some.inj same
              apply False.elim
              apply notAll
              simpa only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using wanted.2

/-- Constructor provenance excludes the negative list index in retainAtomic. -/
theorem atomic_size_positive (buckets : List (Input Symbol Value)) (size : Nat)
    (selected : commonAtomicSize buckets = some size)
    (origins : ∀ bucket ∈ buckets,
      StaticSamplingDispatch.Origin bucket.atomic bucket.minimum bucket.data.sizes.plan)
    (live : ∀ bucket ∈ buckets, 0 < count bucket.data.sizes.plan) : 0 < size := by
  obtain ⟨nonempty, every⟩ := (commonAtomicSize_exact buckets size).mp selected
  cases buckets with
  | nil => contradiction
  | cons first rest =>
      obtain ⟨actual, positive, minimum, _⟩ := StaticSamplingDispatch.origin_atomic
        (origins first (by simp)) (every first (by simp)).1 (live first (by simp))
      have same := (every first (by simp)).2
      rw [minimum] at same
      cases Option.some.inj same
      exact positive

/-- Presence of one retained table selects the weighted-class branch before atom retention. -/
theorem retained_priority (first second : Input Symbol Value) (rest : List (Input Symbol Value))
    (retained : hasMasses (first :: second :: rest) = true) :
    mode (first :: second :: rest) = .retained ∧
      merge (first :: second :: rest) = FinalSizeFields.regularMerge ((first :: second :: rest).map Input.data) ∧
      mergedAtomic (first :: second :: rest) = false := by
  simp [mode, merge, mergedAtomic, retained]

/-- An all-atomic common-size merge uses global conditional masses only without retained tables. -/
theorem atomic_branch (first second : Input Symbol Value) (rest : List (Input Symbol Value)) (size : Nat)
    (absent : hasMasses (first :: second :: rest) = false)
    (atoms : commonAtomicSize (first :: second :: rest) = some size) :
    mode (first :: second :: rest) = .atomic size ∧
      merge (first :: second :: rest) = FinalSizeFields.atomicMerge size ((first :: second :: rest).map Input.data) ∧
      mergedAtomic (first :: second :: rest) = true := by
  simp [mode, merge, mergedAtomic, absent, atoms]

/-- Mixed markers or unequal minimum sizes take the ordinary class-count merge. -/
theorem ordinary_branch (first second : Input Symbol Value) (rest : List (Input Symbol Value))
    (absent : hasMasses (first :: second :: rest) = false)
    (atoms : commonAtomicSize (first :: second :: rest) = none) :
    mode (first :: second :: rest) = .ordinary ∧
      merge (first :: second :: rest) = FinalSizeFields.regularMerge ((first :: second :: rest).map Input.data) ∧
      mergedAtomic (first :: second :: rest) = false := by
  simp [mode, merge, mergedAtomic, absent, atoms]

/-- The flag dispatcher constructs aligned count and class fields on every successful branch. -/
theorem merge_aligned (buckets : List (Input Symbol Value)) (nonempty : buckets ≠ [])
    (aligned : ∀ bucket ∈ buckets, FinalSizeFields.Aligned bucket.data)
    (global : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.data.global)
    (positive : ∀ bucket ∈ buckets, ∀ entry ∈ bucket.data.global.conditional, 0 < entry.1) :
    FinalSizeFields.Aligned (merge buckets) := by
  have allAligned : ∀ bucket ∈ buckets.map Input.data, FinalSizeFields.Aligned bucket := by
    intro bucket member
    obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
    exact aligned input present
  have allGlobal : ∀ bucket ∈ buckets.map Input.data, FinalObservationMass.Valid bucket.global := by
    intro bucket member
    obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
    exact global input present
  have allPositive : ∀ bucket ∈ buckets.map Input.data, ∀ entry ∈ bucket.global.conditional, 0 < entry.1 := by
    intro bucket member
    obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
    exact positive input present
  unfold merge
  split
  · exact aligned _ (by simp)
  · split
    · exact FinalSizeFields.regularMerge_aligned _ allAligned
    · split
      · exact FinalSizeFields.atomicMerge_aligned _ _ (by simpa using nonempty) allGlobal allPositive
      · exact FinalSizeFields.regularMerge_aligned _ allAligned

/-- All branch choices retain the exact same global decoder and declared conditional law. -/
theorem merge_global (buckets : List (Input Symbol Value)) :
    (merge buckets).global = FinalObservationMass.merge (buckets.map (fun bucket => bucket.data.global)) := by
  unfold merge
  split
  · rfl
  · split
    · simp [FinalSizeFields.regularMerge, List.map_map, Function.comp_def]
    · split <;> simp [FinalSizeFields.regularMerge, FinalSizeFields.atomicMerge, List.map_map, Function.comp_def]

/-- Retained table presence is exactly the source any-isJust test. -/
theorem hasMasses_exact (buckets : List (Input Symbol Value)) :
    hasMasses buckets = true ↔ ∃ bucket ∈ buckets, bucket.data.sizes.retained.isSome = true := by
  simp [hasMasses, List.any_eq_true]

/-- The retained branch stores the sum of the original unnormalized class masses. -/
theorem retained_mass (first second : Input Symbol Value) (rest : List (Input Symbol Value))
    (retained : hasMasses (first :: second :: rest) = true)
    (valid : ∀ bucket ∈ first :: second :: rest, Valid bucket.data.sizes) (size : Nat) :
    massAt (merge (first :: second :: rest)).sizes size =
      ((first :: second :: rest).map (fun bucket => massAt bucket.data.sizes size)).sum := by
  rw [(retained_priority first second rest retained).2.1]
  have sumMass := FiniteSizeSampling.choice_retained_mass
    ((first :: second :: rest).map (fun bucket => bucket.data.sizes))
    (by
      intro record member
      obtain ⟨bucket, present, rfl⟩ := List.mem_map.mp member
      exact valid bucket present)
    (by simpa [hasMasses, List.any_map] using retained) size
  simpa [FinalSizeFields.regularMerge, OpenGroupedSize.merge, List.map_map, Function.comp_def] using sumMass

/-- A non-singleton merge has a retained table exactly when at least one input does. -/
theorem retained_flag (first second : Input Symbol Value) (rest : List (Input Symbol Value)) :
    (merge (first :: second :: rest)).sizes.retained.isSome = hasMasses (first :: second :: rest) := by
  have regular : (FinalSizeFields.regularMerge ((first :: second :: rest).map Input.data)).sizes.retained.isSome =
      hasMasses (first :: second :: rest) := by
    simp only [FinalSizeFields.regularMerge, List.map_cons, OpenGroupedSize.merge, choice, finish,
      List.any_cons, List.any_map, Function.comp_def, hasMasses]
    cases flag : (first.data.sizes.retained.isSome ||
      (second.data.sizes.retained.isSome || rest.any (fun bucket => bucket.data.sizes.retained.isSome))) <;>
      simp
  cases retained : hasMasses (first :: second :: rest) with
  | true => rw [(retained_priority first second rest retained).2.1]; exact regular.trans retained
  | false =>
      cases atoms : commonAtomicSize (first :: second :: rest) with
      | none => rw [(ordinary_branch first second rest retained atoms).2.1]; exact regular.trans retained
      | some size =>
          rw [(atomic_branch first second rest size retained atoms).2.1]
          rfl

/-- Global validity and count alignment derive the live-atom condition used by retainAtomic. -/
theorem selected_size_positive (buckets : List (Input Symbol Value)) (size : Nat)
    (selected : commonAtomicSize buckets = some size)
    (origins : ∀ bucket ∈ buckets,
      StaticSamplingDispatch.Origin bucket.atomic bucket.minimum bucket.data.sizes.plan)
    (aligned : ∀ bucket ∈ buckets, FinalSizeFields.Aligned bucket.data)
    (global : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.data.global) : 0 < size := by
  apply atomic_size_positive buckets size selected origins
  intro bucket member
  rw [(aligned bucket member).count, ← (global bucket member).count]
  exact StaticSamplingDispatch.probability_live _ (global bucket member).probability

/-- The modeled fixed-size atomic branch agrees with the actual atom-plus-pays field construction. -/
theorem source_atomic_fields (first second : Input Symbol Value) (rest : List (Input Symbol Value))
    (size : Nat) (absent : hasMasses (first :: second :: rest) = false)
    (selected : commonAtomicSize (first :: second :: rest) = some size)
    (origins : ∀ bucket ∈ first :: second :: rest,
      StaticSamplingDispatch.Origin bucket.atomic bucket.minimum bucket.data.sizes.plan)
    (aligned : ∀ bucket ∈ first :: second :: rest, FinalSizeFields.Aligned bucket.data)
    (global : ∀ bucket ∈ first :: second :: rest, FinalObservationMass.Valid bucket.data.global) :
    let source := StaticSamplingDispatch.paySteps (size - 1)
      (atomic 1 (merge (first :: second :: rest)).global.conditional)
    count source.plan = (merge (first :: second :: rest)).global.conditional.length ∧
      (∀ found, classRanks source.plan found = classRanks (merge (first :: second :: rest)).sizes.plan found) ∧
      (∀ found, source.weights found = (merge (first :: second :: rest)).sizes.weights found) := by
  have positive := selected_size_positive _ size selected origins aligned global
  rw [(atomic_branch first second rest size absent selected).2.1]
  exact StaticSamplingDispatch.retainAtomic_exact size positive _

/-- Every successful dispatcher branch has the finite all-and-only class decoder. -/
theorem class_decoder (buckets : List (Input Symbol Value)) (nonempty : buckets ≠ [])
    (aligned : ∀ bucket ∈ buckets, FinalSizeFields.Aligned bucket.data)
    (global : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.data.global)
    (positive : ∀ bucket ∈ buckets, ∀ entry ∈ bucket.data.global.conditional, 0 < entry.1)
    (size rank : Nat) :
    (∃ term, OpenGroupedSize.selectClass (merge buckets).global.index (merge buckets).sizes size rank = some term) ↔
      rank < (classRanks (merge buckets).sizes.plan size).length := by
  have validGlobal : FinalObservationMass.Valid (merge buckets).global := by
    rw [merge_global]
    apply FinalObservationMass.merge_valid _ (by simpa using nonempty)
    intro bucket member
    obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
    exact global input present
  exact OpenGroupedSize.selectClass_exists _ validGlobal.ranks _
    (merge_aligned buckets nonempty aligned global positive).count size rank

/-- Every dispatched live size class has a positive normalized sampler with unique original ranks. -/
theorem class_probability (buckets : List (Input Symbol Value)) (nonempty : buckets ≠ [])
    (aligned : ∀ bucket ∈ buckets, FinalSizeFields.Aligned bucket.data)
    (global : ∀ bucket ∈ buckets, FinalObservationMass.Valid bucket.data.global)
    (positive : ∀ bucket ∈ buckets, ∀ entry ∈ bucket.data.global.conditional, 0 < entry.1)
    (size : Nat) (live : classRanks (merge buckets).sizes.plan size ≠ []) :
    IsProbability (FiniteSizeSampling.sample (merge buckets).sizes size) ∧
      ((FiniteSizeSampling.sample (merge buckets).sizes size).map Prod.snd).Nodup := by
  have valid := (merge_aligned buckets nonempty aligned global positive).sizes
  exact ⟨FiniteSizeSampling.sample_probability _ valid size live,
    (FiniteSizeSampling.sample_ranks _ valid size).2⟩

end MicroCFTA.BucketMergeDispatch
