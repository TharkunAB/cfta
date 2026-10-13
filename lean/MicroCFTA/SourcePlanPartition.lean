import MicroCFTA.SourcePlanPositions

/-!
# Exact finite size-class partition

The class lists are built independently of position conversion. Each member
occurs once, in exactly one size class. Position conversion and class lookup
are inverses in both directions.
-/
namespace MicroCFTA.SourcePlanPartition
open SourcePlanPositions SizedRank

/-- A listed member converts to a position in that same size class. -/
theorem member_position (plan : Plan) (size rank : Nat)
    (member : rank ∈ classRanks plan size) :
    ∃ part, position plan rank = some part ∧ part.size = size := by
  induction plan generalizing size rank with
  | select total | selectOnDemand total =>
      simp only [classRanks] at member
      split at member
      next same =>
        exact ⟨⟨1, rank⟩, by simp [position, List.mem_range.mp member], same.symm⟩
      next different => simp at member
  | pure =>
      simp only [classRanks] at member
      split at member
      next same =>
        have zero : rank = 0 := by simpa using member
        exact ⟨⟨0, 0⟩, by simp [position, zero], same.symm⟩
      next different => simp at member
  | pay inner ih =>
      cases size with
      | zero => simp [classRanks] at member
      | succ size =>
          obtain ⟨part, found, same⟩ := ih size rank member
          exact ⟨⟨part.size + 1, part.rank⟩, by simp [position, found], by simpa using same⟩
  | scale factor positive inner ih =>
      simp only [classRanks] at member
      split at member
      next divisible =>
        obtain ⟨part, found, same⟩ := ih (size / factor) rank member
        refine ⟨⟨factor * part.size, part.rank⟩, by simp [position, found], ?_⟩
        change factor * part.size = size
        rw [same]
        have := Nat.mod_add_div size factor
        omega
      next absent => simp at member
  | shared inner ih | map inner ih => exact ih size rank member
  | choice left right ihl ihr =>
      rcases List.mem_append.mp member with first | second
      · obtain ⟨part, found, same⟩ := ihl size rank first
        exact ⟨part, by simp [position, class_rank_bound left size rank first, found], same⟩
      · obtain ⟨original, present, rfl⟩ := List.mem_map.mp second
        obtain ⟨part, found, same⟩ := ihr size original present
        exact ⟨⟨part.size, (classRanks left part.size).length + part.rank⟩,
          by simp [position, show ¬count left + original < count left by omega, found], same⟩
  | ap left right ihl ihr =>
      obtain ⟨split, within, present⟩ := List.mem_flatMap.mp member
      simp only [Decoder.applyValues, List.mem_flatMap, List.mem_map] at present
      obtain ⟨function, ⟨first, firstMember, firstSame⟩, second, secondMember, same⟩ := present
      subst function
      subst rank
      obtain ⟨firstPart, firstFound, firstSize⟩ := ihl split first firstMember
      obtain ⟨secondPart, secondFound, secondSize⟩ := ihr (size - split) second secondMember
      have secondBound := class_rank_bound right _ second secondMember
      have bounded := Probability.pairRank_lt (class_rank_bound left _ first firstMember) secondBound
      have splitPair := Probability.split_pair secondBound (left := first)
      refine ⟨productPosition (fun size => (classRanks left size).length)
        (fun size => (classRanks right size).length) firstPart secondPart, ?_, ?_⟩
      · have divided := congrArg Prod.fst splitPair
        have remainder := congrArg Prod.snd splitPair
        simp only [Probability.splitRank] at divided remainder
        simp [position, bounded, divided, remainder, firstFound, secondFound]
      · have splitBound := List.mem_range.mp within
        simp only [productPosition_size]
        omega
  | sized classes bound =>
      change rank ∈ PlanVariants.sizedRanks classes bound size at member
      simp only [PlanVariants.sizedRanks] at member
      split at member
      next within =>
        obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
        exact ⟨⟨size, index⟩,
          PlanVariants.position_sized_offset classes bound ⟨size, index⟩ within
            (List.mem_range.mp present), rfl⟩
      next outside => simp at member

/-- The independent class lists cannot put one original rank at two sizes. -/
theorem class_size_unique (plan : Plan) (first second rank : Nat)
    (left : rank ∈ classRanks plan first) (right : rank ∈ classRanks plan second) :
    first = second := by
  obtain ⟨a, ha, sa⟩ := member_position plan first rank left
  obtain ⟨b, hb, sb⟩ := member_position plan second rank right
  have same := Option.some.inj (ha.symm.trans hb)
  subst b
  exact sa.symm.trans sb

/-- No size class repeats an original member rank. -/
theorem class_nodup (plan : Plan) (size : Nat) : (classRanks plan size).Nodup := by
  induction plan generalizing size with
  | select total | selectOnDemand total =>
      by_cases same : size = 1 <;> simp [classRanks, same, List.nodup_range]
  | pure => by_cases same : size = 0 <;> simp [classRanks, same]
  | pay inner ih => cases size <;> simp [classRanks, ih]
  | scale factor positive inner ih =>
      simp only [classRanks]
      split
      · exact ih (size / factor)
      · simp
  | shared inner ih | map inner ih => exact ih size
  | choice left right ihl ihr =>
      apply List.nodup_append.mpr
      refine ⟨ihl size, List.pairwise_map.mpr ((ihr size).imp ?_), ?_⟩
      · intro a b different same
        exact different (Nat.add_left_cancel same)
      · intro a ha b hb same
        obtain ⟨other, present, rfl⟩ := List.mem_map.mp hb
        have bound := class_rank_bound left size a ha
        omega
  | ap left right ihl ihr =>
      simp only [classRanks, Decoder.applyValues, List.flatMap_map]
      apply List.pairwise_flatMap.mpr
      constructor
      · intro split present
        apply List.pairwise_flatMap.mpr
        constructor
        · intro first firstMember
          apply List.pairwise_map.mpr
          apply List.Pairwise.imp_of_mem _ (ihr (size - split))
          intro a b ha hb different same
          exact different (Probability.pairRank_injective
            (class_rank_bound right _ a ha) (class_rank_bound right _ b hb) same).2
        · apply List.Pairwise.imp_of_mem _ (ihl split)
          intro first second hf hs different a ha b hb same
          obtain ⟨ra, hra, rfl⟩ := List.mem_map.mp ha
          obtain ⟨rb, hrb, rfl⟩ := List.mem_map.mp hb
          exact different (Probability.pairRank_injective
            (class_rank_bound right _ ra hra) (class_rank_bound right _ rb hrb) same).1
      · apply List.Pairwise.imp_of_mem _ (RecursiveSize.range_ordered (size + 1))
        intro firstSplit secondSplit hf hs different a ha b hb same
        obtain ⟨la, hla, ra, hra, rfl⟩ := (by simpa only [List.mem_flatMap, List.mem_map] using ha :
          ∃ la, la ∈ classRanks left firstSplit ∧ ∃ ra, ra ∈ classRanks right (size - firstSplit) ∧
            Probability.pairRank (count right) la ra = a)
        obtain ⟨lb, hlb, rb, hrb, rfl⟩ := (by simpa only [List.mem_flatMap, List.mem_map] using hb :
          ∃ lb, lb ∈ classRanks left secondSplit ∧ ∃ rb, rb ∈ classRanks right (size - secondSplit) ∧
            Probability.pairRank (count right) lb rb = b)
        have leftEq := (Probability.pairRank_injective
          (class_rank_bound right _ ra hra) (class_rank_bound right _ rb hrb) same).1
        subst lb
        have sizes := class_size_unique left firstSplit secondSplit la hla hlb
        omega
  | sized classes bound =>
      simp only [classRanks, PlanVariants.classRanks, PlanVariants.sizedRanks]
      split
      · apply List.pairwise_map.mpr
        apply List.Pairwise.imp _ List.nodup_range
        intro a b different same
        exact different (Nat.add_left_cancel same)
      · simp

/-- Every stored class position converts back to that exact position. -/
theorem position_class_lookup (plan : Plan) (part : Position) (rank : Nat)
    (found : (classRanks plan part.size)[part.rank]? = some rank) :
    position plan rank = some part := by
  have present := List.mem_of_getElem? found
  obtain ⟨actual, converted, sameSize⟩ := member_position plan part.size rank present
  have replay := position_replay plan rank actual converted
  rw [sameSize] at replay
  have sameRank := (class_nodup plan part.size).eq_of_getElem?_eq
    (List.getElem?_eq_some_iff.mp found).1 (found.trans replay.symm)
  have same : actual = part := by
    cases actual
    cases part
    simp_all
  simpa [same] using converted

/-- Class lookup and source position conversion are inverse operations. -/
theorem position_iff_lookup (plan : Plan) (part : Position) (rank : Nat) :
    position plan rank = some part ↔ (classRanks plan part.size)[part.rank]? = some rank :=
  ⟨position_replay plan rank part, position_class_lookup plan part rank⟩

/-- The finite classes contain all valid original ranks and only those ranks. -/
theorem partition_exact (plan : Plan) (rank : Nat) :
    (∃ size, rank ∈ classRanks plan size) ↔ rank < count plan := by
  constructor
  · rintro ⟨size, member⟩
    exact class_rank_bound plan size rank member
  · intro valid
    obtain ⟨part, found⟩ := position_complete plan rank valid
    exact ⟨part.size, List.mem_of_getElem? (position_replay plan rank part found)⟩

/-- A structural upper bound for every member size of a finite plan. -/
def maxSize : Plan → Nat
  | .select _ | .selectOnDemand _ => 1
  | .pure => 0
  | .pay inner => maxSize inner + 1
  | .scale factor _ inner => factor * maxSize inner
  | .shared inner | .map inner => maxSize inner
  | .choice left right => max (maxSize left) (maxSize right)
  | .ap left right => maxSize left + maxSize right
  | .sized _ bound => bound

/-- Every nonempty class lies within the computed finite size bound. -/
theorem class_size_bound (plan : Plan) (size rank : Nat)
    (member : rank ∈ classRanks plan size) : size ≤ maxSize plan := by
  induction plan generalizing size rank with
  | select total | selectOnDemand total =>
      simp only [classRanks] at member
      split at member
      next same => simp [maxSize, same]
      next different => simp at member
  | pure =>
      simp only [classRanks] at member
      split at member
      next same => simp [maxSize, same]
      next different => simp at member
  | pay inner ih =>
      cases size with
      | zero => simp [classRanks] at member
      | succ size => exact Nat.succ_le_succ (ih size rank member)
  | scale factor positive inner ih =>
      simp only [classRanks] at member
      split at member
      next divisible =>
        have childBound := ih (size / factor) rank member
        have scaled := Nat.mul_le_mul_left factor childBound
        have restored : factor * (size / factor) = size := by
          have := Nat.mod_add_div size factor
          omega
        simpa only [maxSize, restored] using scaled
      next absent => simp at member
  | shared inner ih | map inner ih => exact ih size rank member
  | choice left right ihl ihr =>
      rcases List.mem_append.mp member with first | second
      · exact Nat.le_trans (ihl size rank first) (Nat.le_max_left _ _)
      · obtain ⟨original, present, same⟩ := List.mem_map.mp second
        exact Nat.le_trans (ihr size original present) (Nat.le_max_right _ _)
  | ap left right ihl ihr =>
      obtain ⟨split, within, present⟩ := List.mem_flatMap.mp member
      simp only [Decoder.applyValues, List.mem_flatMap, List.mem_map] at present
      obtain ⟨function, ⟨first, firstMember, firstSame⟩, second, secondMember, same⟩ := present
      have firstBound := ihl split first firstMember
      have secondBound := ihr (size - split) second secondMember
      have splitBound := List.mem_range.mp within
      simp only [maxSize]
      omega
  | sized classes bound =>
      change rank ∈ PlanVariants.sizedRanks classes bound size at member
      simp only [PlanVariants.sizedRanks] at member
      split at member
      next within => exact within
      next outside => simp at member

/-- Enumerate original ranks in size-major order through all finite classes. -/
def allRanks (plan : Plan) : List Nat :=
  (List.range (maxSize plan + 1)).flatMap (classRanks plan)

/-- The computed finite size bound includes every original rank. -/
theorem allRanks_member (plan : Plan) (rank : Nat) :
    rank ∈ allRanks plan ↔ rank < count plan := by
  constructor
  · intro member
    obtain ⟨size, _, present⟩ := List.mem_flatMap.mp member
    exact class_rank_bound plan size rank present
  · intro valid
    obtain ⟨size, present⟩ := (partition_exact plan rank).mpr valid
    exact List.mem_flatMap.mpr ⟨size,
      List.mem_range.mpr (by have bound := class_size_bound plan size rank present; omega), present⟩

/-- Size-major traversal repeats no member within or between classes. -/
theorem allRanks_nodup (plan : Plan) : (allRanks plan).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun size _ => class_nodup plan size, ?_⟩
  apply List.Pairwise.imp _ (RecursiveSize.range_ordered (maxSize plan + 1))
  intro first second before a ha b hb same
  subst b
  have sizes := class_size_unique plan first second a ha hb
  omega

/-- Finite size-major traversal is a permutation of the entire rank interval. -/
theorem allRanks_perm (plan : Plan) : (allRanks plan).Perm (List.range (count plan)) := by
  apply (List.perm_ext_iff_of_nodup (allRanks_nodup plan) List.nodup_range).mpr
  intro rank
  simpa only [List.mem_range] using allRanks_member plan rank

/-- The sum of all finite size counts is exactly the ordinary member count. -/
theorem class_count_total (plan : Plan) :
    ((List.range (maxSize plan + 1)).map (fun size => (classRanks plan size).length)).sum = count plan := by
  have lengths := (allRanks_perm plan).length_eq
  simpa only [allRanks, List.length_flatMap, List.length_range] using lengths

example : allRanks (.choice (.pay .pure) .pure) = [1, 0] := by cbv
example : allRanks (.ap (.choice .pure (.pay .pure)) (.choice (.pay .pure) .pure)) = [1, 0, 3, 2] := by cbv

end MicroCFTA.SourcePlanPartition
