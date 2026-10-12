import MicroCFTA.KeyedTermMass
import MicroCFTA.KeyedSourceUnfolding
import MicroCFTA.RecursiveSamplerUnfolding

/-!
# Full simultaneous grouped sampler equations

The source reads a tied family at every key. The executable model reads only
smaller sizes. A guarded product can expose an unmatched current-size child
only beside an empty sibling. That sibling has zero key mass and no ranks.
-/
namespace MicroCFTA.KeyedSamplerUnfolding
open KeyedSource SamplerReplay
open KeyedTermMass (SameGroup map_left_group map_right_group merge_same apply_group empty_group)
open RecursiveRankMass (Related ranked_projection)

/-- Empty grouped classes have zero retained mass, by the local live-mass invariant. -/
theorem zero_mass (group : GroupedRecord.Group α) (valid : GroupedRecord.Valid group)
    (zero : Decoder.count group.members.plan = 0) : group.mass = 0 := by
  have notPositive : ¬0 < group.mass := by
    intro positive
    have live := valid.2.2.mp positive
    omega
  exact Rat.le_antisymm (Rat.not_lt.mp notPositive) valid.2.1

/-- An empty left class removes both product mass and every right-component sampler effect. -/
theorem empty_left (left : GroupedRecord.Group (α → β)) (right : GroupedRecord.Group α)
    (otherLeft : GroupedRecord.Group (γ → δ)) (otherRight : GroupedRecord.Group γ)
    (leftValid : GroupedRecord.Valid left) (otherValid : GroupedRecord.Valid otherLeft)
    (leftZero : Decoder.count left.members.plan = 0) (otherZero : Decoder.count otherLeft.members.plan = 0) :
    SameGroup (GroupedRecord.apply left right) (GroupedRecord.apply otherLeft otherRight) := by
  constructor
  · simp [GroupedRecord.apply, zero_mass left leftValid leftZero, zero_mass otherLeft otherValid otherZero]
  · exact RecursiveSamplerUnfolding.empty_left_same _ _ _ _ leftValid.1.1 otherValid.1.1 leftZero otherZero

/-- An empty right class removes both product mass and every left-component sampler effect. -/
theorem empty_right (left : GroupedRecord.Group (α → β)) (right : GroupedRecord.Group α)
    (otherLeft : GroupedRecord.Group (γ → δ)) (otherRight : GroupedRecord.Group γ)
    (rightValid : GroupedRecord.Valid right) (otherValid : GroupedRecord.Valid otherRight)
    (rightZero : Decoder.count right.members.plan = 0) (otherZero : Decoder.count otherRight.members.plan = 0) :
    SameGroup (GroupedRecord.apply left right) (GroupedRecord.apply otherLeft otherRight) := by
  constructor
  · simp [GroupedRecord.apply, zero_mass right rightValid rightZero, zero_mass otherRight otherValid otherZero]
  · exact RecursiveSamplerUnfolding.empty_right_same _ _ _ _ rightValid.1.1 otherValid.1.1 rightZero otherZero

/-- The actual grouped minima exclude a zero-size body class. -/
theorem zero_count (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root) (recipe : Recipe Key Root α)
    (environment : Key → GroupedRecord.Classes Root)
    (sound : ∀ key size value, value ∈ Decoder.values (environment key size).members.plan →
      Derives program (program key) value size)
    (nonzero : (GroupedMinimum.evaluate (minimumExpr recipe) (minima keys complete program)).join ≠ some 0) :
    Decoder.count (record recipe environment 0).members.plan = 0 := by
  rw [Decoder.count_correct, record_values,
    KeyedSourceUnfolding.zero_empty keys complete program recipe _ sound nonzero]
  rfl

/-- Guarded body construction preserves key masses and rank laws under smaller-size agreement. -/
theorem records_agree (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root) (budget : Nat)
    (first second : Key → GroupedRecord.Classes Root)
    (firstSound : ∀ key size value, value ∈ Decoder.values (first key size).members.plan → Derives program (program key) value size)
    (secondSound : ∀ key size value, value ∈ Decoder.values (second key size).members.plan → Derives program (program key) value size)
    (firstValid : ∀ key size, GroupedRecord.Valid (first key size)) (secondValid : ∀ key size, GroupedRecord.Valid (second key size))
    (agree : ∀ key size, size < budget → SameGroup (first key size) (second key size))
    (recipe : Recipe Key Root α) (size : Nat) :
    (size < budget → SameGroup (record recipe first size) (record recipe second size)) ∧
      (size ≤ budget → guarded recipe (minima keys complete program) = true →
        SameGroup (record recipe first size) (record recipe second size)) := by
  induction recipe generalizing size with
  | finite source | retained mass positive source => exact ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  | occurrence key => exact ⟨agree key size, by simp [guarded]⟩
  | map transform inner ih =>
      exact ⟨fun within => map_right_group _ _ _ (map_left_group _ _ _ ((ih size).1 within)),
        fun within guard => map_right_group _ _ _ (map_left_group _ _ _ ((ih size).2 within guard))⟩
  | pay inner ih =>
      cases size with
      | zero => exact ⟨fun _ => empty_group, fun _ _ => empty_group⟩
      | succ size => exact ⟨fun within => (ih size).1 (by omega), fun within _ => (ih size).1 (by omega)⟩
  | choice left right ihl ihr =>
      exact ⟨fun within => merge_same _ _ (.cons ((ihl size).1 within) (.cons ((ihr size).1 within) .nil)),
        fun within guard => merge_same _ _
          (.cons ((ihl size).2 within (Bool.and_eq_true_iff.mp guard).1)
            (.cons ((ihr size).2 within (Bool.and_eq_true_iff.mp guard).2) .nil))⟩
  | ap functions arguments ihf iha =>
      have lift (size : Nat) (steps : ∀ split ∈ List.range (size + 1),
          SameGroup (GroupedRecord.apply (record functions first split) (record arguments first (size - split)))
            (GroupedRecord.apply (record functions second split) (record arguments second (size - split)))) :
          SameGroup (record (.ap functions arguments) first size) (record (.ap functions arguments) second size) := by
        apply merge_same
        have related : ∀ splits : List Nat, (∀ split ∈ splits, split ∈ List.range (size + 1)) →
            Related SameGroup
              (splits.map fun split => GroupedRecord.apply (record functions first split) (record arguments first (size - split)))
              (splits.map fun split => GroupedRecord.apply (record functions second split) (record arguments second (size - split))) := by
          intro splits
          induction splits with
          | nil => intro _; exact .nil
          | cons split rest ih =>
              intro included
              exact .cons (steps split (included split (by simp))) (ih (fun n mem => included n (by simp [mem])))
        exact related _ (fun _ mem => mem)
      constructor
      · intro within
        apply lift
        intro split member
        have bound : split ≤ size := by have := List.mem_range.mp member; omega
        exact apply_group _ _ _ _ ((ihf split).1 (by omega)) ((iha (size - split)).1 (by omega))
      · intro within guard
        apply lift
        intro split member
        have bound : split ≤ size := by have := List.mem_range.mp member; omega
        have both := Bool.and_eq_true_iff.mp guard
        have firstPart : SameGroup (record functions first split) (record functions second split) ∨
            (Decoder.count (record arguments first (size - split)).members.plan = 0 ∧
              Decoder.count (record arguments second (size - split)).members.plan = 0) := by
          rcases Bool.or_eq_true_iff.mp both.1 with guarded | positive
          · exact Or.inl ((ihf split).2 (by omega) guarded)
          · by_cases smaller : split < budget
            · exact Or.inl ((ihf split).1 smaller)
            · have zero : size - split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_count keys complete program arguments first firstSound (of_decide_eq_true positive),
                zero_count keys complete program arguments second secondSound (of_decide_eq_true positive)⟩
        have secondPart : SameGroup (record arguments first (size - split)) (record arguments second (size - split)) ∨
            (Decoder.count (record functions first split).members.plan = 0 ∧
              Decoder.count (record functions second split).members.plan = 0) := by
          rcases Bool.or_eq_true_iff.mp both.2 with guarded | positive
          · exact Or.inl ((iha (size - split)).2 (by omega) guarded)
          · by_cases smaller : size - split < budget
            · exact Or.inl ((iha (size - split)).1 smaller)
            · have zero : split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_count keys complete program functions first firstSound (of_decide_eq_true positive),
                zero_count keys complete program functions second secondSound (of_decide_eq_true positive)⟩
        rcases firstPart with firstSame | emptyRight
        · rcases secondPart with secondSame | emptyLeft
          · exact apply_group _ _ _ _ firstSame secondSame
          · exact empty_left _ _ _ _ (record_valid _ _ firstValid _) (record_valid _ _ secondValid _)
              emptyLeft.1 emptyLeft.2
        · exact empty_right _ _ _ _ (record_valid _ _ firstValid _) (record_valid _ _ secondValid _)
            emptyRight.1 emptyRight.2

/-- Every guarded family class satisfies the source's full key-mass, count, and rank-probability equation. -/
theorem family_unfold (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true) (size : Nat) (key : Key) :
    SameGroup (family program size key)
      (record (program key) (fun childKey childSize => family program childSize childKey) size) := by
  let earlier : Key → GroupedRecord.Classes Root := fun childKey childSize =>
    if childSize < size then family program childSize childKey else GroupedRecord.empty
  have sound : ∀ childKey childSize value, value ∈ Decoder.values (family program childSize childKey).members.plan →
      Derives program (program childKey) value childSize :=
    fun childKey childSize value => (family_exact keys complete program accepted childSize childKey value).mp
  have earlierSound : ∀ childKey childSize value, value ∈ Decoder.values (earlier childKey childSize).members.plan →
      Derives program (program childKey) value childSize := by
    intro childKey childSize value member
    dsimp only [earlier] at member
    split at member
    · exact sound childKey childSize value member
    · simp [GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values] at member
  have earlierValid : ∀ childKey childSize, GroupedRecord.Valid (earlier childKey childSize) := by
    intro childKey childSize
    dsimp only [earlier]
    split
    · exact family_valid program childSize childKey
    · exact GroupedRecord.empty_valid
  have agree : ∀ childKey childSize, childSize < size →
      SameGroup (earlier childKey childSize) (family program childSize childKey) := by
    intro childKey childSize smaller
    simp only [earlier, ite_eq_left smaller]
    exact ⟨rfl, rfl, rfl⟩
  have step := (records_agree keys complete program size earlier (fun childKey childSize => family program childSize childKey)
    earlierSound sound earlierValid (fun childKey childSize => family_valid program childSize childKey)
    agree (program key) size).2 (Nat.le_refl size) (accepted key)
  rw [family]
  simpa only [earlier, dite_eq_ite] using step

/-- The complete ranked sampler agrees with the full source knot, even when sampled values repeat. -/
theorem ranked_unfold (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true) (size : Nat) (key : Key) :
    (family program size key).members.sampling.ranked =
      (record (program key) (fun childKey childSize => family program childSize childKey) size).members.sampling.ranked := by
  have decoder : ∀ rank, (Decoder.decode (family program size key).members.plan rank).map id =
      Decoder.decode (record (program key) (fun childKey childSize => family program childSize childKey) size).members.plan rank := by
    intro rank
    rw [Option.map_id, Decoder.decode_correct, Decoder.decode_correct, record_values]
    exact congrArg (fun items : List Root => items[rank]?)
      (KeyedSourceUnfolding.family_unfold_values keys complete program accepted size key)
  have result := ranked_projection id _ _ _ _ (family_valid program size key).1.1.2
    (record_valid (program key) _ (fun childKey childSize => family_valid program childSize childKey) size).1.1.2
    decoder (family_unfold keys complete program accepted size key).2.2
  simpa [Probability.map] using result

/-- The value sampler and unnormalized key mass satisfy the same full simultaneous equations. -/
theorem fields_unfold (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true) (size : Nat) (key : Key) :
    (family program size key).mass =
      (record (program key) (fun childKey childSize => family program childSize childKey) size).mass ∧
    (family program size key).members.sampling.values =
      (record (program key) (fun childKey childSize => family program childSize childKey) size).members.sampling.values := by
  refine ⟨(family_unfold keys complete program accepted size key).1, ?_⟩
  rw [← (family_valid program size key).1.1.1,
    ← (record_valid (program key) _ (fun childKey childSize => family_valid program childSize childKey) size).1.1.1,
    ranked_unfold keys complete program accepted size key]

end MicroCFTA.KeyedSamplerUnfolding
