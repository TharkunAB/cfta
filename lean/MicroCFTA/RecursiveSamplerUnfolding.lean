import MicroCFTA.RecursiveSourceUnfolding
import MicroCFTA.RecursiveRankMass

/-!
# Exact sampler unfolding at guarded recursive knots

Zero-count product components discard the other component's rank law.
This permits the same guard argument as ordered class unfolding. It proves
the full source count and sampler equations without evaluating an infinite
family or identifying equal user values.
-/
namespace MicroCFTA.RecursiveSamplerUnfolding
open RecursiveSource SamplerReplay RecursiveRankMass

/-- A zero-count record with valid replay has no ranked sampler outcomes. -/
theorem zero_rankMass (record : Record α) (coherent : Coherent record)
    (zero : Decoder.count record.plan = 0) : rankMass record = [] := by
  have empty : record.sampling.ranked = [] := by
    cases found : record.sampling.ranked with
    | nil => rfl
    | cons entry rest =>
        have selected := coherent.2 entry (by simp [found])
        have bound := decoded_bound record.plan _ _ selected
        omega
  simp [rankMass, empty, Probability.map]

/-- An empty left product discards every right rank and mass. -/
theorem empty_left_same (left : Record (α → β)) (right : Record α)
    (otherLeft : Record (γ → δ)) (otherRight : Record γ)
    (leftValid : Coherent left) (otherValid : Coherent otherLeft)
    (leftZero : Decoder.count left.plan = 0) (otherZero : Decoder.count otherLeft.plan = 0) :
    Same (applyRecord left right) (applyRecord otherLeft otherRight) := by
  constructor
  · simp [applyRecord, Decoder.count, leftZero, otherZero]
  · simp [apply_rankMass, zero_rankMass left leftValid leftZero,
      zero_rankMass otherLeft otherValid otherZero, Probability.product, Probability.map]

/-- An empty right product discards every left rank and mass. -/
theorem empty_right_same (left : Record (α → β)) (right : Record α)
    (otherLeft : Record (γ → δ)) (otherRight : Record γ)
    (rightValid : Coherent right) (otherValid : Coherent otherRight)
    (rightZero : Decoder.count right.plan = 0) (otherZero : Decoder.count otherRight.plan = 0) :
    Same (applyRecord left right) (applyRecord otherLeft otherRight) := by
  constructor
  · simp [applyRecord, Decoder.count, rightZero, otherZero]
  · simp only [apply_rankMass, zero_rankMass right rightValid rightZero,
      zero_rankMass otherRight otherValid otherZero, Probability.product, List.map_nil]
    rw [List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl), List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)]
    rfl

/-- The proved positive minimum excludes the complete zero-size record. -/
theorem zero_count (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (recipe : Recipe Root α)
    (environment : Nat → Record Root)
    (sound : ∀ size value, value ∈ Decoder.values (environment size).plan → Derives body body value size)
    (nonzero : minimum recipe assumed ≠ some 0) : Decoder.count (record recipe environment 0).plan = 0 := by
  rw [Decoder.count_correct, record_values,
    RecursiveSourceUnfolding.zero_empty body assumed fixed recipe _ sound nonzero]
  rfl

/-- Source guards preserve counts and rank probabilities under smaller-size environment agreement. -/
theorem records_agree (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (budget : Nat)
    (first second : Nat → Record Root)
    (firstSound : ∀ size value, value ∈ Decoder.values (first size).plan → Derives body body value size)
    (secondSound : ∀ size value, value ∈ Decoder.values (second size).plan → Derives body body value size)
    (firstLive : ∀ size, LiveValid (first size)) (secondLive : ∀ size, LiveValid (second size))
    (agree : ∀ size, size < budget → Same (first size) (second size))
    (recipe : Recipe Root α) (size : Nat) :
    (size < budget → Same (record recipe first size) (record recipe second size)) ∧
      (size ≤ budget → guarded recipe assumed = true → Same (record recipe first size) (record recipe second size)) := by
  induction recipe generalizing size with
  | finite source => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  | occurrence => exact ⟨agree size, by simp [guarded]⟩
  | map transform inner ih =>
      exact ⟨fun within => map_right _ _ _ (map_left _ _ _ ((ih size).1 within)),
        fun within guard => map_right _ _ _ (map_left _ _ _ ((ih size).2 within guard))⟩
  | pay inner ih =>
      cases size with
      | zero => exact ⟨fun _ => empty_same, fun _ _ => empty_same⟩
      | succ size => exact ⟨fun within => (ih size).1 (by omega), fun within _ => (ih size).1 (by omega)⟩
  | choice left right ihl ihr =>
      exact ⟨fun within => choice_same _ _ (.cons ((ihl size).1 within) (.cons ((ihr size).1 within) .nil)),
        fun within guard => choice_same _ _
          (.cons ((ihl size).2 within (Bool.and_eq_true_iff.mp guard).1)
            (.cons ((ihr size).2 within (Bool.and_eq_true_iff.mp guard).2) .nil))⟩
  | ap functions arguments ihf iha =>
      have lift (size : Nat) (steps : ∀ split ∈ List.range (size + 1),
          Same (applyRecord (record functions first split) (record arguments first (size - split)))
            (applyRecord (record functions second split) (record arguments second (size - split)))) :
          Same (record (.ap functions arguments) first size) (record (.ap functions arguments) second size) := by
        apply choice_same
        have related : ∀ splits : List Nat, (∀ split ∈ splits, split ∈ List.range (size + 1)) →
            Related Same
              (splits.map fun split => applyRecord (record functions first split) (record arguments first (size - split)))
              (splits.map fun split => applyRecord (record functions second split) (record arguments second (size - split))) := by
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
        exact apply_same _ _ _ _ ((ihf split).1 (by omega)) ((iha (size - split)).1 (by omega))
      · intro within guard
        apply lift
        intro split member
        have bound : split ≤ size := by have := List.mem_range.mp member; omega
        have both := Bool.and_eq_true_iff.mp guard
        have firstPart : Same (record functions first split) (record functions second split) ∨
            (Decoder.count (record arguments first (size - split)).plan = 0 ∧
              Decoder.count (record arguments second (size - split)).plan = 0) := by
          rcases Bool.or_eq_true_iff.mp both.1 with guarded | positive
          · exact Or.inl ((ihf split).2 (by omega) guarded)
          · by_cases smaller : split < budget
            · exact Or.inl ((ihf split).1 smaller)
            · have zero : size - split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_count body assumed fixed arguments first firstSound (of_decide_eq_true positive),
                zero_count body assumed fixed arguments second secondSound (of_decide_eq_true positive)⟩
        have secondPart : Same (record arguments first (size - split)) (record arguments second (size - split)) ∨
            (Decoder.count (record functions first split).plan = 0 ∧
              Decoder.count (record functions second split).plan = 0) := by
          rcases Bool.or_eq_true_iff.mp both.2 with guarded | positive
          · exact Or.inl ((iha (size - split)).2 (by omega) guarded)
          · by_cases smaller : size - split < budget
            · exact Or.inl ((iha (size - split)).1 smaller)
            · have zero : split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_count body assumed fixed functions first firstSound (of_decide_eq_true positive),
                zero_count body assumed fixed functions second secondSound (of_decide_eq_true positive)⟩
        rcases firstPart with firstSame | emptyRight
        · rcases secondPart with secondSame | emptyLeft
          · exact apply_same _ _ _ _ firstSame secondSame
          · exact empty_left_same _ _ _ _ (record_live _ _ _ firstLive).1 (record_live _ _ _ secondLive).1
              emptyLeft.1 emptyLeft.2
        · exact empty_right_same _ _ _ _ (record_live _ _ _ firstLive).1 (record_live _ _ _ secondLive).1
            emptyRight.1 emptyRight.2

/-- The compiled family has the full source knot's count and exact rank law. -/
theorem family_unfold (body : Recipe Root Root)
    (accepted : guarded body (assumption body) = true) (size : Nat) :
    Same (family body size) (record body (family body) size) := by
  let earlier : Nat → Record Root := fun childSize =>
    if childSize < size then family body childSize else FiniteSource.empty
  have sound : ∀ childSize value, value ∈ Decoder.values (family body childSize).plan →
      Derives body body value childSize := fun childSize value => (family_exact body accepted childSize value).mp
  have earlierSound : ∀ childSize value, value ∈ Decoder.values (earlier childSize).plan →
      Derives body body value childSize := by
    intro childSize value member
    dsimp only [earlier] at member
    split at member
    · exact sound childSize value member
    · simp [FiniteSource.empty, SamplerReplay.source, Decoder.values] at member
  have earlierLive : ∀ childSize, LiveValid (earlier childSize) := by
    intro childSize
    dsimp only [earlier]
    split
    · exact family_live body childSize
    · exact FiniteSource.empty_live
  have agree : ∀ childSize, childSize < size → Same (earlier childSize) (family body childSize) := by
    intro childSize smaller
    simp only [earlier, ite_eq_left smaller]
    exact ⟨rfl, rfl⟩
  have step := (records_agree body (assumption body) (assumption_fixed body) size earlier (family body)
    earlierSound sound earlierLive (family_live body) agree body size).2 (Nat.le_refl size) accepted
  rw [family]
  simpa only [earlier, dite_eq_ite] using step

/-- The ranked sampler satisfies the full source knot equation, including every value and mass. -/
theorem ranked_unfold (body : Recipe Root Root)
    (accepted : guarded body (assumption body) = true) (size : Nat) :
    (family body size).sampling.ranked = (record body (family body) size).sampling.ranked := by
  have decoder : ∀ rank, (Decoder.decode (family body size).plan rank).map id =
      Decoder.decode (record body (family body) size).plan rank := by
    intro rank
    rw [Option.map_id, Decoder.decode_correct, Decoder.decode_correct, record_values]
    exact congrArg (fun items : List Root => items[rank]?)
      (RecursiveSourceUnfolding.family_unfold_values body accepted size)
  have result := ranked_projection id _ _ _ _ (family_live body size).1.2
    (record_live body (family body) size (family_live body)).1.2 decoder (family_unfold body accepted size).2
  simpa [Probability.map] using result

/-- The value-only sampler also satisfies the full source knot equation. -/
theorem sampler_unfold (body : Recipe Root Root)
    (accepted : guarded body (assumption body) = true) (size : Nat) :
    (family body size).sampling.values = (record body (family body) size).sampling.values := by
  rw [← (family_live body size).1.1,
    ← (record_live body (family body) size (family_live body)).1.1, ranked_unfold body accepted size]

end MicroCFTA.RecursiveSamplerUnfolding
