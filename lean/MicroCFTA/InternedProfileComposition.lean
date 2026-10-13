import MicroCFTA.InternedProfileHeap
import MicroCFTA.InternedRootProfileNode
import MicroCFTA.InternedOccurrenceObservations

/-!
# Ordered source result profiles compose

Source child lists retain one profile relation at each original position.
The same relation determines both union profiles and ordinary live-edge
decisions. It also retains the exact order of the child computations.
-/
namespace MicroCFTA.InternedProfileComposition
open InternedConstructorTemplates InternedRootProfile InternedProfileEquivalence
open InternedOccurrenceObservations (Paired)
open InternedProfileSemantics (isEmpty combineMany)

/-- Ordered completed source values agree with their abstract profiles. -/
abbrev Matches (values : List (Value Symbol Guard)) (profiles : List Profile) : Prop :=
  Paired (fun value abstract => Equivalent (profile value) abstract) values profiles

/-- Equivalent profiles have the same empty-list case. -/
theorem empty_same {first second : Profile} (same : Equivalent first second) : first = some [] ↔ second = some [] := by
  constructor
  · intro firstEmpty
    subst first
    cases second with
    | none => simp [Equivalent] at same
    | some names =>
        cases names with
        | nil => rfl
        | cons head rest => have impossible := (same.2 head).mpr (by simp); simp at impossible
  · intro secondEmpty
    subst second
    cases first with
    | none => simp [Equivalent] at same
    | some names =>
        cases names with
        | nil => rfl
        | cons head rest => have impossible := (same.2 head).mp (by simp); simp at impossible

/-- The pure interpreter's empty decision depends only on profile equivalence. -/
theorem isEmpty_same {first second : Profile} (same : Equivalent first second) : isEmpty first = isEmpty second := by
  have decision : ∀ value : Profile, isEmpty value = true ↔ value = some [] := by
    intro value
    cases value with
    | none => simp [isEmpty]
    | some names => cases names <;> simp [isEmpty]
  apply Bool.eq_iff_iff.mpr
  rw [decision, decision]
  exact empty_same same

/-- Union profile composition preserves equivalence in both arguments. -/
theorem combine_same {first second otherFirst otherSecond : Profile}
    (left : Equivalent first otherFirst) (right : Equivalent second otherSecond) :
    Equivalent (combine first second) (combine otherFirst otherSecond) := by
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
                  constructor
                  · simp [combine]
                  · intro name
                    have firstMember : name ∈ first ↔ name ∈ otherFirst := left.2 name
                    have secondMember : name ∈ second ↔ name ∈ otherSecond := right.2 name
                    simp [combine, firstMember, secondMember]

/-- The source list profile agrees with the pure union fold of matched children. -/
theorem many_matched {values : List (Value Symbol Guard)} {profiles : List Profile} (matched : Matches values profiles) :
    Equivalent (many values) (combineMany profiles) := by
  have sameCombine : ∀ first second : Profile, InternedProfileSemantics.combine first second = combine first second := by
    intro first second
    cases first <;> cases second <;> rfl
  induction matched with
  | nil => simp [many, combineMany, Equivalent]
  | cons head tail ih =>
      rw [many, combineMany, sameCombine]
      exact combine_same head ih

/-- Matched child profiles make the same source live-edge decision. -/
theorem children_matched {values : List (Value Symbol Guard)} {profiles : List Profile} (matched : Matches values profiles) :
    values.all (fun child => !isEmpty (profile child)) = profiles.all (fun child => !isEmpty child) := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.all_cons, isEmpty_same head, ih]

end MicroCFTA.InternedProfileComposition
