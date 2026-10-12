import MicroCFTA.KeyedSource

/-!
# Ordered unfolding of guarded recursive source classes

The executable class compiler cuts recursive reads at the current size.
The source knot reads the full family. The guard and computed minimum make
those two environments equal for the complete ordered body output. The
proof retains duplicate members and their positions.
-/
namespace MicroCFTA.KeyedSourceUnfolding
open KeyedSource

/-- A positive or absent minimum excludes every size-zero body member. -/
theorem zero_empty (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root) (recipe : Recipe Key Root α)
    (environment : Key → Nat → List Root)
    (sound : ∀ key size value, value ∈ environment key size → Derives program (program key) value size)
    (nonzero : (GroupedMinimum.evaluate (minimumExpr recipe) (minima keys complete program)).join ≠ some 0) : values recipe environment 0 = [] := by
  cases found : values recipe environment 0 with
  | nil => rfl
  | cons value rest =>
      have derived := values_sound program recipe environment sound 0 value (by simp [found])
      obtain ⟨lower, read, bound⟩ := derivation_minimum keys complete program recipe value 0 derived
      have zero : lower = 0 := by omega
      exact False.elim (nonzero (by simp [read, zero]))

/-- Agreement below a budget extends to a guarded body at that budget, in list order. -/
theorem values_agree (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root) (budget : Nat)
    (first second : Key → Nat → List Root)
    (firstSound : ∀ key size value, value ∈ first key size → Derives program (program key) value size)
    (secondSound : ∀ key size value, value ∈ second key size → Derives program (program key) value size)
    (agree : ∀ key size, size < budget → first key size = second key size)
    (recipe : Recipe Key Root α) (size : Nat) :
    (size < budget → values recipe first size = values recipe second size) ∧
      (size ≤ budget → guarded recipe (minima keys complete program) = true → values recipe first size = values recipe second size) := by
  induction recipe generalizing size with
  | finite source | retained mass positive source => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | occurrence key => exact ⟨agree key size, by simp [guarded]⟩
  | map transform inner ih =>
      exact ⟨fun within => congrArg (List.map transform) ((ih size).1 within),
        fun within guard => congrArg (List.map transform) ((ih size).2 within guard)⟩
  | pay inner ih =>
      cases size with
      | zero => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
      | succ size => exact ⟨fun within => (ih size).1 (by omega), fun within _ => (ih size).1 (by omega)⟩
  | choice left right ihl ihr =>
      constructor
      · intro within
        simp only [values, (ihl size).1 within, (ihr size).1 within]
      · intro within guard
        have both := Bool.and_eq_true_iff.mp guard
        simp only [values, (ihl size).2 within both.1, (ihr size).2 within both.2]
  | ap functions arguments ihf iha =>
      constructor
      · intro within
        simp only [values]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro split member
        have bound : split ≤ size := by have := List.mem_range.mp member; omega
        rw [(ihf split).1 (by omega), (iha (size - split)).1 (by omega)]
      · intro within guard
        have both := Bool.and_eq_true_iff.mp guard
        simp only [values]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro split member
        have bound : split ≤ size := by have := List.mem_range.mp member; omega
        have firstPart : values functions first split = values functions second split ∨
            (values arguments first (size - split) = [] ∧ values arguments second (size - split) = []) := by
          rcases Bool.or_eq_true_iff.mp both.1 with guarded | positive
          · exact Or.inl ((ihf split).2 (by omega) guarded)
          · by_cases smaller : split < budget
            · exact Or.inl ((ihf split).1 smaller)
            · have zero : size - split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_empty keys complete program arguments first firstSound (of_decide_eq_true positive),
                zero_empty keys complete program arguments second secondSound (of_decide_eq_true positive)⟩
        have secondPart : values arguments first (size - split) = values arguments second (size - split) ∨
            (values functions first split = [] ∧ values functions second split = []) := by
          rcases Bool.or_eq_true_iff.mp both.2 with guarded | positive
          · exact Or.inl ((iha (size - split)).2 (by omega) guarded)
          · by_cases smaller : size - split < budget
            · exact Or.inl ((iha (size - split)).1 smaller)
            · have zero : split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_empty keys complete program functions first firstSound (of_decide_eq_true positive),
                zero_empty keys complete program functions second secondSound (of_decide_eq_true positive)⟩
        rcases firstPart with firstEqual | bothEmpty
        · rcases secondPart with secondEqual | bothEmpty
          · rw [firstEqual, secondEqual]
          · simp [Decoder.applyValues, bothEmpty.1, bothEmpty.2]
        · simp only [Decoder.applyValues, bothEmpty.1, bothEmpty.2, List.map_nil]
          exact (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).trans
            (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).symm

/-- A guarded keyed class equals its full simultaneous source unfolding. -/
theorem languageClass_unfold (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true)
    (size : Nat) (key : Key) :
    languageClass program size key =
      values (program key) (fun childKey childSize => languageClass program childSize childKey) size := by
  have sound : ∀ key size value, value ∈ languageClass program size key → Derives program (program key) value size := by
    intro key size value member
    exact (family_exact keys complete program accepted size key value).mp (by simpa [family_values] using member)
  rw [languageClass]
  apply (values_agree keys complete program size _ _ _ sound _ (program key) size).2
    (Nat.le_refl size) (accepted key)
  · intro childKey childSize value member
    split at member
    · exact sound childKey childSize value member
    · simp at member
  · intro childKey childSize smaller
    simp [smaller]

/-- Every keyed finite class record has the full source knot's ordered values. -/
theorem family_unfold_values (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true)
    (size : Nat) (key : Key) :
    Decoder.values (family program size key).members.plan =
      values (program key) (fun childKey childSize => Decoder.values (family program childSize childKey).members.plan) size := by
  simpa only [family_values] using languageClass_unfold keys complete program accepted size key

end MicroCFTA.KeyedSourceUnfolding
