import MicroCFTA.RecursiveSource

/-!
# Ordered unfolding of guarded recursive source classes

The executable class compiler cuts recursive reads at the current size.
The source knot reads the full family. The guard and computed minimum make
those two environments equal for the complete ordered body output. The
proof retains duplicate members and their positions.
-/
namespace MicroCFTA.RecursiveSourceUnfolding
open RecursiveSource

/-- A positive or absent minimum excludes every size-zero body member. -/
theorem zero_empty (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (recipe : Recipe Root α)
    (environment : Nat → List Root)
    (sound : ∀ size value, value ∈ environment size → Derives body body value size)
    (nonzero : minimum recipe assumed ≠ some 0) : values recipe environment 0 = [] := by
  cases found : values recipe environment 0 with
  | nil => rfl
  | cons value rest =>
      have derived := values_sound body recipe environment sound 0 value (by simp [found])
      obtain ⟨lower, read, bound⟩ := derives_minimum body assumed fixed recipe value 0 derived
      have zero : lower = 0 := by omega
      exact False.elim (nonzero (by simpa [zero] using read))

/-- Agreement below a budget extends to a guarded body at that budget, in list order. -/
theorem values_agree (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (budget : Nat)
    (first second : Nat → List Root)
    (firstSound : ∀ size value, value ∈ first size → Derives body body value size)
    (secondSound : ∀ size value, value ∈ second size → Derives body body value size)
    (agree : ∀ size, size < budget → first size = second size)
    (recipe : Recipe Root α) (size : Nat) :
    (size < budget → values recipe first size = values recipe second size) ∧
      (size ≤ budget → guarded recipe assumed = true → values recipe first size = values recipe second size) := by
  induction recipe generalizing size with
  | finite source => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | occurrence => exact ⟨agree size, by simp [guarded]⟩
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
              exact Or.inr ⟨zero_empty body assumed fixed arguments first firstSound (of_decide_eq_true positive),
                zero_empty body assumed fixed arguments second secondSound (of_decide_eq_true positive)⟩
        have secondPart : values arguments first (size - split) = values arguments second (size - split) ∨
            (values functions first split = [] ∧ values functions second split = []) := by
          rcases Bool.or_eq_true_iff.mp both.2 with guarded | positive
          · exact Or.inl ((iha (size - split)).2 (by omega) guarded)
          · by_cases smaller : size - split < budget
            · exact Or.inl ((iha (size - split)).1 smaller)
            · have zero : split = 0 := by omega
              rw [zero]
              exact Or.inr ⟨zero_empty body assumed fixed functions first firstSound (of_decide_eq_true positive),
                zero_empty body assumed fixed functions second secondSound (of_decide_eq_true positive)⟩
        rcases firstPart with firstEqual | bothEmpty
        · rcases secondPart with secondEqual | bothEmpty
          · rw [firstEqual, secondEqual]
          · simp [Decoder.applyValues, bothEmpty.1, bothEmpty.2]
        · simp only [Decoder.applyValues, bothEmpty.1, bothEmpty.2, List.map_nil]
          exact (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).trans
            (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).symm

/-- A guarded recursive class equals one source unfolding over its full class family. -/
theorem languageClass_unfold (body : Recipe Root Root)
    (accepted : guarded body (assumption body) = true) (size : Nat) :
    languageClass body size = values body (languageClass body) size := by
  have sound : ∀ size value, value ∈ languageClass body size → Derives body body value size := by
    intro size value member
    exact (family_exact body accepted size value).mp (by simpa [family_values] using member)
  rw [languageClass]
  apply (values_agree body (assumption body) (assumption_fixed body) size _ _ _ sound _ body size).2
    (Nat.le_refl size) accepted
  · intro childSize value member
    split at member
    · exact sound childSize value member
    · simp at member
  · intro childSize smaller
    simp [smaller]

/-- The finite class record has the full source knot's ordered body values. -/
theorem family_unfold_values (body : Recipe Root Root)
    (accepted : guarded body (assumption body) = true) (size : Nat) :
    Decoder.values (family body size).plan = values body (fun size => Decoder.values (family body size).plan) size := by
  simpa only [family_values] using languageClass_unfold body accepted size

end MicroCFTA.RecursiveSourceUnfolding
