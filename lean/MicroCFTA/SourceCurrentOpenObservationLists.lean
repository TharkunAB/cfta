import MicroCFTA.SourceCurrentOpenObservations

/-!
# Root-list algebra for finite open observations

Append combines two related root lists. Root membership determines every
reference and row origin. These laws require no heap invariant.
-/
namespace MicroCFTA.SourceCurrentOpenObservationLists
open InternedConstructorTemplates SourceCurrentOpenObservations
open MergedFreshOrdinaryGraph

private theorem reference_append [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (first second : List (Value Symbol Guard))
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view (first ++ second) name ↔
      ReferenceOrigin view first name ∨ ReferenceOrigin view second name := by
  rw [reference_seeds, reference_seeds, reference_seeds]
  constructor
  · rintro ⟨value, member, actual⟩
    rcases List.mem_append.mp member with left | right
    · exact Or.inl ⟨value, left, actual⟩
    · exact Or.inr ⟨value, right, actual⟩
  · rintro (⟨value, member, actual⟩ | ⟨value, member, actual⟩)
    · exact ⟨value, List.mem_append_left second member, actual⟩
    · exact ⟨value, List.mem_append_right first member, actual⟩

private theorem origin_append [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (first second : List (Value Symbol Guard))
    (row : EdgeValue Symbol Guard) :
    Origin view (first ++ second) row ↔ Origin view first row ∨ Origin view second row := by
  rw [origin_seeds, origin_seeds, origin_seeds]
  constructor
  · rintro ⟨value, member, actual⟩
    rcases List.mem_append.mp member with left | right
    · exact Or.inl ⟨value, left, actual⟩
    · exact Or.inr ⟨value, right, actual⟩
  · rintro (⟨value, member, actual⟩ | ⟨value, member, actual⟩)
    · exact ⟨value, List.mem_append_left second member, actual⟩
    · exact ⟨value, List.mem_append_right first member, actual⟩

/-- Append retains both reference observations and full row matches. -/
theorem append [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (firstLeft firstRight secondLeft secondRight : List (Value Symbol Guard))
    (first : Same depth view firstLeft firstRight)
    (second : Same depth view secondLeft secondRight) :
    Same depth view (firstLeft ++ secondLeft) (firstRight ++ secondRight) := by
  cases depth with
  | zero =>
      intro name
      rw [reference_append, reference_append]
      exact or_congr (first name) (second name)
  | succ depth =>
      refine ⟨?_, ?_, ?_⟩
      · intro name
        rw [reference_append, reference_append]
        exact or_congr (first.1 name) (second.1 name)
      · intro row origin
        rcases (origin_append view firstLeft secondLeft row).mp origin with left | right
        · obtain ⟨other, present, matched⟩ := first.2.1 row left
          exact ⟨other, (origin_append view firstRight secondRight other).mpr (Or.inl present), matched⟩
        · obtain ⟨other, present, matched⟩ := second.2.1 row right
          exact ⟨other, (origin_append view firstRight secondRight other).mpr (Or.inr present), matched⟩
      · intro row origin
        rcases (origin_append view firstRight secondRight row).mp origin with left | right
        · obtain ⟨other, present, matched⟩ := first.2.2 row left
          exact ⟨other, (origin_append view firstLeft secondLeft other).mpr (Or.inl present), matched⟩
        · obtain ⟨other, present, matched⟩ := second.2.2 row right
          exact ⟨other, (origin_append view firstLeft secondLeft other).mpr (Or.inr present), matched⟩

/-- Equal root membership retains every finite open observation. -/
theorem of_members [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (first second : List (Value Symbol Guard))
    (members : ∀ value, value ∈ first ↔ value ∈ second) : Same depth view first second := by
  apply of_origins depth view first second
  · intro name
    rw [reference_seeds, reference_seeds]
    constructor
    · rintro ⟨value, member, actual⟩
      exact ⟨value, (members value).mp member, actual⟩
    · rintro ⟨value, member, actual⟩
      exact ⟨value, (members value).mpr member, actual⟩
  · intro row
    rw [origin_seeds, origin_seeds]
    constructor
    · rintro ⟨value, member, actual⟩
      exact ⟨value, (members value).mp member, actual⟩
    · rintro ⟨value, member, actual⟩
      exact ⟨value, (members value).mpr member, actual⟩

end MicroCFTA.SourceCurrentOpenObservationLists
