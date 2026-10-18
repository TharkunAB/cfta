import MicroCFTA.SourceCurrentOpenObservationSurvival

/-!
# Physical survival and observations at one reader

The relation uses one fixed observation heap. It also retains physical
Empty agreement. Actual node and union calls preserve this relation when
their immediate children or members satisfy it. No reader transport,
binder congruence, or root-filter congruence is stated here.
-/
namespace MicroCFTA.SourceCurrentReaderObservations
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedFacts (Facts)
open InternedNestedProvenance (Values Edges)
open InternedStoredMuOrigins (Normal)
open SourceCurrentOpenObservations (Same RowMatch)
open Language

/-- Related values agree on physical emptiness and all finite observations at one reader. -/
def Related [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (first second : Value Symbol Guard) : Prop :=
  (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧
    ∀ depth, Same depth view [first] [second]

/-- Each value has the same physical emptiness and observations as itself. -/
theorem Related.refl [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) (value : Value Symbol Guard) : Related view value value :=
  ⟨Iff.rfl,fun depth => Same.refl depth view [value]⟩

/-- Reader-relative agreement is symmetric. -/
theorem Related.symm [DecidableEq (EdgeKey Symbol Guard)]
    {view : State Symbol Guard} {first second : Value Symbol Guard}
    (related : Related view first second) : Related view second first :=
  ⟨related.1.symm,fun depth => (related.2 depth).symm⟩

/-- Reader-relative agreement composes at the same fixed reader. -/
theorem Related.trans [DecidableEq (EdgeKey Symbol Guard)]
    {view : State Symbol Guard} {first middle last : Value Symbol Guard}
    (left : Related view first middle) (right : Related view middle last) : Related view first last :=
  ⟨left.1.trans right.1,fun depth => (left.2 depth).trans (right.2 depth)⟩

/-- Agreement at every view restricts to the selected reader. -/
theorem of_uniform [DecidableEq (EdgeKey Symbol Guard)]
    (view : State Symbol Guard) {first second : Value Symbol Guard}
    (related : SourceCurrentOpenObservationSurvival.Related first second) : Related view first second :=
  ⟨related.1,fun depth => related.2 depth view⟩

private theorem children_empty [DecidableEq (EdgeKey Symbol Guard)]
    {view : State Symbol Guard}
    {first second : List (Value Symbol Guard)} (paired : All₂ (Related view) first second) :
    first.any (fun value => value.referenceOf == .empty) =
      second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | @cons first second rest remaining pair tail ih =>
      have head : (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
        by_cases empty : first.referenceOf = .empty
        · simp only [empty, pair.1.mp empty, beq_self_eq_true]
        · have other : second.referenceOf ≠ .empty := fun found => empty (pair.1.mpr found)
          simp only [beq_eq_false_iff_ne.mpr empty, beq_eq_false_iff_ne.mpr other]
      simp only [List.any_cons, head, ih]

private theorem all_empty [DecidableEq (EdgeKey Symbol Guard)]
    {view : State Symbol Guard}
    {first second : List (Value Symbol Guard)} (paired : All₂ (Related view) first second) :
    (∀ value ∈ first, value.referenceOf = .empty) ↔
      ∀ value ∈ second, value.referenceOf = .empty := by
  induction paired with
  | nil => exact Iff.rfl
  | cons pair tail ih =>
      constructor
      · intro all value member
        rcases List.mem_cons.mp member with rfl | later
        · exact pair.1.mp (all _ List.mem_cons_self)
        · exact ih.mp (fun value included => all value (List.mem_cons_of_mem _ included)) value later
      · intro all value member
        rcases List.mem_cons.mp member with rfl | later
        · exact pair.1.mpr (all _ List.mem_cons_self)
        · exact ih.mpr (fun value included => all value (List.mem_cons_of_mem _ included)) value later

/-- Actual node construction derives matching survival tests from its original related rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (first second : List (EdgeValue Symbol Guard)) (firstState secondState : State Symbol Guard)
    (firstFacts : Facts firstState) (secondFacts : Facts secondState)
    (firstResident : Edges firstState first) (secondResident : Edges secondState second)
    (forward : ∀ row ∈ first, ∃ other ∈ second, RowMatch (Related view) row other)
    (backward : ∀ row ∈ second, ∃ other ∈ first, RowMatch (Related view) row other) :
    Related view (run (InternedConstructorTemplates.makeNode first) firstState).1
      (run (InternedConstructorTemplates.makeNode second) secondState).1 := by
  constructor
  · rw [InternedEmptyNormalization.makeNode_empty_iff first firstState firstFacts.coherent firstFacts.linked firstResident,
      InternedEmptyNormalization.makeNode_empty_iff second secondState secondFacts.coherent secondFacts.linked secondResident]
    constructor
    · intro all row member
      obtain ⟨other, included, fields⟩ := backward row member
      rw [children_empty fields.2.2]
      exact all other included
    · intro all row member
      obtain ⟨other, included, fields⟩ := forward row member
      rw [children_empty fields.2.2]
      exact all other included
  · have matched (depth : Nat) := by
        apply SourceCurrentOpenObservationConstructors.makeNode depth view firstState secondState first second
          firstFacts secondFacts firstResident secondResident
        · intro row member
          obtain ⟨other, included, fields⟩ := forward row (List.mem_filter.mp member).1
          refine ⟨other, List.mem_filter.mpr ⟨included, ?_⟩, fields.1, fields.2.1,
            All₂.imp (fun _ _ relation => relation.2 depth) fields.2.2⟩
          have alive := (List.mem_filter.mp member).2
          change (!(other.children.any (fun child => child.referenceOf == .empty))) = true
          rw [← children_empty fields.2.2]
          exact alive
        · intro row member
          obtain ⟨other, included, fields⟩ := backward row (List.mem_filter.mp member).1
          refine ⟨other, List.mem_filter.mpr ⟨included, ?_⟩, fields.1, fields.2.1,
            All₂.imp (fun _ _ relation => relation.2 depth) fields.2.2⟩
          have alive := (List.mem_filter.mp member).2
          change (!(other.children.any (fun child => child.referenceOf == .empty))) = true
          rw [← children_empty fields.2.2]
          exact alive
    intro depth
    cases depth with
    | zero => exact (matched 0).lower
    | succ depth => exact matched depth

/-- Actual union construction preserves physical emptiness and observations at the fixed reader. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (first second : List (Value Symbol Guard)) (firstState secondState : State Symbol Guard)
    (firstNormal : Normal firstState) (secondNormal : Normal secondState)
    (firstAvailable : Values firstState first) (secondAvailable : Values secondState second)
    (paired : All₂ (Related view) first second) :
    Related view (run (InternedConstructorTemplates.makeUnion first) firstState).1
      (run (InternedConstructorTemplates.makeUnion second) secondState).1 := by
  constructor
  · rw [InternedEmptyNormalization.makeUnion_empty_iff first firstState firstNormal.facts.coherent
      firstNormal.facts.linked firstNormal.live firstNormal.proper firstAvailable,
      InternedEmptyNormalization.makeUnion_empty_iff second secondState secondNormal.facts.coherent
      secondNormal.facts.linked secondNormal.live secondNormal.proper secondAvailable]
    exact all_empty paired
  · intro depth
    exact SourceCurrentOpenObservationConstructors.makeUnion depth view firstState secondState first second
      firstNormal.facts secondNormal.facts firstNormal.live secondNormal.live
      firstAvailable secondAvailable (All₂.imp (fun _ _ pair => pair.2 depth) paired)

end MicroCFTA.SourceCurrentReaderObservations
