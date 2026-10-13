import MicroCFTA.InternedObservedAbsence

/-!
# Exact paired root self filtering

Two root unions can use different local recursive references. If each
union contains its own reference and their retained member lists agree,
both source filters execute the same ordinary constructor request.
-/
namespace MicroCFTA.InternedPairedSelfFilter
open Cache InternedConstructorTemplates InternedObservedAbsence InternedOccurrenceObservations
open InternedBinderProtocol (Reference NodeKey NodeRef)
open InternedRecordCoherence InternedProbeProvenance InternedNestedFacts InternedLiveEdges InternedBoundaryAtoms

/-- A root union that contains its own reference executes exactly the filtered union request. -/
theorem filter_present (name : Reference) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (present : .reference name ∈ members) :
    withoutSelfReference name (.union entry members depth free) =
      makeUnion (members.filter (fun value => value.referenceOf != .ref name)) := by
  have selected : members.any (fun value => value.referenceOf == .ref name) = true :=
    List.any_eq_true.mpr ⟨.reference name, present, by simp [Value.referenceOf]⟩
  simp [withoutSelfReference, selected]

/-- Both deleting branches return equal complete values in their actual common cache extension. -/
theorem deleting_same [DecidableEq (EdgeKey Symbol Guard)] (firstName secondName : Reference)
    (firstEntry secondEntry : Interned NodeKey) (firstMembers secondMembers : List (Value Symbol Guard))
    (firstDepth secondDepth : Nat) (firstFree secondFree : List Reference)
    (firstPresent : .reference firstName ∈ firstMembers) (secondPresent : .reference secondName ∈ secondMembers)
    (retainedSame : firstMembers.filter (fun value => value.referenceOf != .ref firstName) =
      secondMembers.filter (fun value => value.referenceOf != .ref secondName))
    (left right common : State Symbol Guard) (lv : Valid left) (rv : Valid right)
    (lg : Grows (run (withoutSelfReference firstName (.union firstEntry firstMembers firstDepth firstFree)) left).2 common)
    (rg : Grows (run (withoutSelfReference secondName (.union secondEntry secondMembers secondDepth secondFree)) right).2 common) :
    (run (withoutSelfReference firstName (.union firstEntry firstMembers firstDepth firstFree)) left).1 =
      (run (withoutSelfReference secondName (.union secondEntry secondMembers secondDepth secondFree)) right).1 := by
  rw [filter_present firstName firstEntry firstMembers firstDepth firstFree firstPresent] at lg ⊢
  rw [filter_present secondName secondEntry secondMembers secondDepth secondFree secondPresent] at rg ⊢
  rw [retainedSame] at lg ⊢
  exact run_shared _ left right common lv rv lg rg

/-- Paired local references disappear while every paired unchanged operand retains its source order. -/
theorem retained_members_same (firstName secondName : Reference)
    (firstMembers secondMembers : List (Value Symbol Guard))
    (paired : Paired (fun first second =>
      (first = .reference firstName ∧ second = .reference secondName) ∨
      (first = second ∧ first ≠ .reference firstName ∧ second ≠ .reference secondName))
      firstMembers secondMembers) :
    firstMembers.filter (fun value => value.referenceOf != .ref firstName) =
      secondMembers.filter (fun value => value.referenceOf != .ref secondName) := by
  induction paired with
  | nil => rfl
  | @cons first second rest tail related paired ih =>
      rcases related with ⟨rfl, rfl⟩ | ⟨rfl, firstDifferent, secondDifferent⟩
      · simpa [Value.referenceOf] using ih
      · have firstKeep : first.referenceOf != .ref firstName :=
          bne_iff_ne.mpr (fun equal => firstDifferent ((referenceOf_self_iff firstName first).mp equal))
        have secondKeep : first.referenceOf != .ref secondName :=
          bne_iff_ne.mpr (fun equal => secondDifferent ((referenceOf_self_iff secondName first).mp equal))
        simp only [List.filter_cons, firstKeep, secondKeep, ↓reduceIte, ih]

/-- Every retained original alternative is clear when the actual filtered root result is clear. -/
theorem retained_clear [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (state : State Symbol Guard)
    (facts : Facts state) (live : Live state) (available : Available state (.union entry members depth free))
    (clear : Clear forbidden (run (withoutSelfReference name (.union entry members depth free)) state).1)
    (value : Value Symbol Guard) (member : value ∈ members) (different : value ≠ .reference name) :
    Clear forbidden value := by
  intro item included
  by_cases present : .reference name ∈ members
  · rw [filter_present name entry members depth free present] at clear
    apply clear item
    apply (makeUnion_atom_iff _ state facts.coherent facts.cached facts.linked live
      (fun child retained => available.children child (List.mem_filter.mp retained).1) item).mpr
    exact ⟨value, (withoutSelfReference_members name members value).mpr ⟨member, different⟩, included⟩
  · rw [withoutSelfReference_absent name entry members depth free present] at clear
    apply clear item
    simpa only [run, atoms] using (many_member members item).mpr ⟨value, member, included⟩

/-- Two absent local names leave the same root union record unchanged, with no cache effects. -/
theorem absent_same [DecidableEq (EdgeKey Symbol Guard)] (firstName secondName : Reference)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (firstAbsent : .reference firstName ∉ members) (secondAbsent : .reference secondName ∉ members)
    (left right : State Symbol Guard) :
    (run (withoutSelfReference firstName (.union entry members depth free)) left).1 =
      (run (withoutSelfReference secondName (.union entry members depth free)) right).1 := by
  rw [withoutSelfReference_absent firstName entry members depth free firstAbsent,
    withoutSelfReference_absent secondName entry members depth free secondAbsent]
  rfl

end MicroCFTA.InternedPairedSelfFilter
