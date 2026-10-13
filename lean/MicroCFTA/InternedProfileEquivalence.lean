import MicroCFTA.InternedProbeDecoder

/-!
# Probe operations respect root profile equivalence

Canonical source unions can remove duplicate references and change their
list order. The probe decisions use only opacity and reference membership.
They therefore preserve the profile equivalence used by source readback.
-/
namespace MicroCFTA.InternedProfileEquivalence
open InternedRootProfile InternedProbeDecoder
open InternedBinderProtocol (Reference)

theorem refl (value : Profile) : Equivalent value value := ⟨Iff.rfl, fun _ => Iff.rfl⟩

theorem symm {first second : Profile} (same : Equivalent first second) : Equivalent second first :=
  ⟨same.1.symm, fun name => (same.2 name).symm⟩

theorem trans {first second third : Profile} (left : Equivalent first second) (right : Equivalent second third) :
    Equivalent first third := ⟨left.1.trans right.1, fun name => (left.2 name).trans (right.2 name)⟩

/-- The all-self decision uses only the set of root references. -/
theorem all_same (first second : List Reference) (name : Reference)
    (same : ∀ reference, reference ∈ first ↔ reference ∈ second) :
    first.all (· == name) = second.all (· == name) := by
  have truth : first.all (· == name) = true ↔ second.all (· == name) = true := by
    simp only [List.all_eq_true]
    constructor
    · intro all reference member
      exact all reference ((same reference).mpr member)
    · intro all reference member
      exact all reference ((same reference).mp member)
  cases left : first.all (· == name) <;> cases right : second.all (· == name) <;> simp_all

/-- Root self normalization preserves equivalent opaque or pure profiles. -/
theorem normalize_same (name : Reference) {first second : Profile} (same : Equivalent first second) :
    Equivalent (normalize name first) (normalize name second) := by
  cases first with
  | none =>
      have secondNone := same.1.mp rfl
      subst second
      exact refl _
  | some left =>
      cases second with
      | none => simp [Equivalent] at same
      | some right =>
          have members : ∀ reference, reference ∈ left ↔ reference ∈ right := same.2
          have all := all_same left right name members
          constructor
          · simp [normalize]
          · intro reference
            cases selected : right.all (· == name) <;> simp [normalize, all, selected, members reference]

/-- Direct-self recognition does not inspect multiplicities or list order. -/
theorem single_same (first second : List Reference) (name : Reference)
    (same : ∀ reference, reference ∈ first ↔ reference ∈ second) : single name first = single name second := by
  have truth : single name first = true ↔ single name second = true := by
    rw [single_iff, single_iff]
    constructor
    · intro selected
      exact ⟨(same name).mp selected.1, fun other member => selected.2 other ((same other).mpr member)⟩
    · intro selected
      exact ⟨(same name).mpr selected.1, fun other member => selected.2 other ((same other).mp member)⟩
  cases left : single name first <;> cases right : single name second <;> simp_all

/-- The decoded smart profile depends only on the two canonical profile equivalence classes. -/
theorem decode_same (firstName secondName : Reference) {first second otherFirst otherSecond : Profile}
    (left : Equivalent first otherFirst) (right : Equivalent second otherSecond) :
    Equivalent (decode firstName secondName first second) (decode firstName secondName otherFirst otherSecond) := by
  cases first with
  | none =>
      have otherNone := left.1.mp rfl
      subst otherFirst
      cases second <;> cases otherSecond <;> exact refl _
  | some first =>
      cases otherFirst with
      | none => simp [Equivalent] at left
      | some otherFirst =>
          cases second with
          | none =>
              have otherNone := right.1.mp rfl
              subst otherSecond
              exact refl _
          | some second =>
              cases otherSecond with
              | none => simp [Equivalent] at right
              | some otherSecond =>
                  have firstSingle := single_same first otherFirst firstName left.2
                  have secondSingle := single_same second otherSecond secondName right.2
                  constructor
                  · simp [decode]
                  · intro name
                    have leftMember : name ∈ first ↔ name ∈ otherFirst := left.2 name
                    have rightMember : name ∈ second ↔ name ∈ otherSecond := right.2 name
                    cases selected : single firstName otherFirst && single secondName otherSecond <;>
                      simp [decode, firstSingle, secondSingle, selected, leftMember, rightMember]

end MicroCFTA.InternedProfileEquivalence
