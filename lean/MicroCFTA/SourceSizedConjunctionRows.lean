import MicroCFTA.SourceSizedConjunctionPositions
import MicroCFTA.SourceSizedConjunctionTuples
import MicroCFTA.SourceSizedEqualChildren

/-!
# Literal equal-child intersection transitions and rows

One transition joins every selected row's equality classes. Each position
receives the conjunction key of its joined group. The constraint retains
the sorted nontrivial groups. Rows use the source first-row/product order.
The local language law describes the computed transition, before worklist
exploration and the later equality-aware canonical sort.
-/
namespace MicroCFTA.SourceSizedConjunctionRows
open Language SourceSizedDecided SourceSizedConjunctionGroupKeys

variable {State Symbol Value Payload : Type}

/-- A child assignment satisfies the row domains and its direct-child equalities. -/
def assignmentHolds (row : Row State Symbol (List (List Nat)))
    (domain : State → Value → Prop) (value : Nat → Value) : Prop :=
  (∀ index state, row.children[index]? = some state → domain state (value index)) ∧
    CompactGroups.GroupsEqual value row.constraint

private theorem tuple_assignment_iff (tuple : List (Row State Symbol (List (List Nat))))
    (domain : State → Value → Prop) (value : Nat → Value) :
    (∀ member ∈ tuple, assignmentHolds member domain value) ↔
      (∀ member ∈ tuple, ∀ index (within : index < member.children.length),
        domain member.children[index] (value index)) ∧
      ∀ member ∈ tuple, ∀ positions ∈ member.constraint, CompactGroups.EqualAt value positions := by
  constructor
  · intro accepted
    exact ⟨fun member memberIn index within =>
      (accepted member memberIn).1 index _ (List.getElem?_eq_getElem within),
      fun member memberIn => (accepted member memberIn).2⟩
  · rintro ⟨domains, equalities⟩ member memberIn
    refine ⟨?_, equalities member memberIn⟩
    intro index state read
    obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp read
    simpa only [same] using domains member memberIn index within

variable [DecidableEq State] [Ord State]

/-- Execute the source intersection of a first transition and its selected tail. -/
def intersection (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) : Row (List State) Symbol (List (List Nat)) :=
  let tuple := first :: others
  let arity := first.children.length
  let groups := CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint)
  ⟨first.label, SourceSizedConjunctionPositions.children tuple arity,
    SourceSizedEqualChildren.classesOf groups⟩

/-- Intersection retains the common source symbol. -/
theorem intersection_label (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) :
    (intersection first others).label = first.label := rfl

/-- Position-map readback retains the first transition's actual arity. -/
theorem intersection_arity (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) :
    (intersection first others).children.length = first.children.length :=
  SourceSizedConjunctionPositions.children_length _ _

/-- Every computed output equality position is bounded by the output arity. -/
theorem intersection_bounded (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) :
    CompactGroups.ValidClasses (intersection first others).children.length
      (intersection first others).constraint := by
  rw [intersection_arity]
  apply SourceSizedEqualChildren.classesOf_bounded
  intro group groupIn index indexIn
  exact List.mem_range.mp ((CompactGroups.childGroups_positions first.children.length _).mem_iff.mp
    (List.mem_flatten.mpr ⟨group, groupIn, indexIn⟩))

/-- Same-token tuples cannot generate an empty reached child key. -/
theorem intersection_nonempty (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat))))
    (arities : ∀ member ∈ first :: others, member.children.length = first.children.length) :
    ∀ key ∈ (intersection first others).children, key ≠ [] :=
  SourceSizedConjunctionPositions.children_nonempty _ _ (List.cons_ne_nil _ _) arities

/-- Every read from the position map names the group containing that position. -/
theorem child_read (tuple : List (Row State Symbol (List (List Nat)))) (arity index : Nat)
    (key : List State) (read : (SourceSizedConjunctionPositions.children tuple arity)[index]? = some key) :
    ∃ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
      index ∈ group ∧ key = groupKey tuple group := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp read
  rw [SourceSizedConjunctionPositions.children_length] at within
  have covered := (CompactGroups.childGroups_positions arity
    (tuple.flatMap fun member => member.constraint)).mem_iff.mpr (List.mem_range.mpr within)
  obtain ⟨group, groupIn, indexIn⟩ := List.mem_flatten.mp covered
  exact ⟨group, groupIn, indexIn, Option.some.inj
    (read.symm.trans (SourceSizedConjunctionPositions.child_at tuple arity group groupIn index indexIn))⟩

/-- The computed transition accepts exactly the intersection of its tuple rows. -/
theorem intersection_exact (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat))))
    (arities : ∀ member ∈ first :: others, member.children.length = first.children.length)
    (valid : CompactGroups.ValidClasses first.children.length
      ((first :: others).flatMap fun member => member.constraint))
    (domain : State → Value → Prop) (value : Nat → Value) :
    assignmentHolds (intersection first others)
      (fun key selected => ∀ state ∈ key, domain state selected) value ↔
      ∀ member ∈ first :: others, assignmentHolds member domain value := by
  let tuple := first :: others
  let arity := first.children.length
  let groups := CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint)
  have selections : assignmentHolds (intersection first others)
        (fun key selected => ∀ state ∈ key, domain state selected) value ↔
      ∀ group ∈ groups, ∃ selected, (∀ state ∈ groupKey tuple group, domain state selected) ∧
        ∀ index ∈ group, value index = selected := by
    change ((∀ index key, (SourceSizedConjunctionPositions.children tuple arity)[index]? = some key →
      ∀ state ∈ key, domain state (value index)) ∧
      CompactGroups.GroupsEqual value (SourceSizedEqualChildren.classesOf groups)) ↔ _
    rw [SourceSizedEqualChildren.classesOf_exact]
    constructor
    · rintro ⟨accepted, equalities⟩ group groupIn
      obtain ⟨index, indexIn⟩ := List.exists_mem_of_ne_nil group
        (CompactGroups.childGroups_nonempty arity _ valid group groupIn)
      refine ⟨value index, accepted index _
        (SourceSizedConjunctionPositions.child_at tuple arity group groupIn index indexIn), ?_⟩
      intro other otherIn
      exact equalities group groupIn other otherIn index indexIn
    · intro selected
      constructor
      · intro index key read state stateIn
        obtain ⟨group, groupIn, indexIn, keyEq⟩ := child_read tuple arity index key read
        obtain ⟨chosen, accepted, repeated⟩ := selected group groupIn
        rw [keyEq] at stateIn
        rw [repeated index indexIn]
        exact accepted state stateIn
      · intro group groupIn left leftIn right rightIn
        obtain ⟨_, _, repeated⟩ := selected group groupIn
        exact (repeated left leftIn).trans (repeated right rightIn).symm
  exact selections.trans
    ((groupSelections_exact tuple domain value arity arities valid).trans
      (tuple_assignment_iff tuple domain value).symm)

/-- Source intersection retains original-key support at every returned child. -/
theorem intersection_supported (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (closed : SourceSizedFiniteKeys.Closed table)
    (first : Row State Symbol (List (List Nat))) (others : List (Row State Symbol (List (List Nat))))
    (stored : ∀ member ∈ first :: others, ∃ owner original,
      original ∈ SourceSizedFiniteKeys.lookup table owner ∧ original.children = member.children) :
    ∀ key ∈ (intersection first others).children, ∀ state ∈ key, state ∈ SourceDenseRows.keys table :=
  SourceSizedConjunctionPositions.children_supported table closed _ _ stored

variable [DecidableEq Symbol]

/-- Compute every transition of one key before the source take(limit+1). -/
def rows (lookup : State → List (Row State Symbol (List (List Nat)))) :
    List State → List (Row (List State) Symbol (List (List Nat)))
  | [] => []
  | owner :: owners => (lookup owner).flatMap fun first =>
      (products (fun state => (lookup state).filter (SourceSizedConjunctionTuples.sameToken first)) owners).map
        (intersection first)

/-- Source rows are exactly intersections of its literal nonempty tuples. -/
theorem mem_rows (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (output : Row (List State) Symbol (List (List Nat))) :
    output ∈ rows lookup key ↔ ∃ first others,
      first :: others ∈ SourceSizedConjunctionTuples.tuples lookup key ∧ intersection first others = output := by
  cases key with
  | nil => simp [rows, SourceSizedConjunctionTuples.tuples]
  | cons owner owners =>
      constructor
      · intro present
        obtain ⟨first, firstIn, member⟩ := List.mem_flatMap.mp present
        obtain ⟨others, othersIn, same⟩ := List.mem_map.mp member
        exact ⟨first, others, List.mem_flatMap.mpr
          ⟨first, firstIn, List.mem_map.mpr ⟨others, othersIn, rfl⟩⟩, same⟩
      · rintro ⟨first, others, tupleIn, same⟩
        obtain ⟨chosen, chosenIn, tailIn⟩ := List.mem_flatMap.mp tupleIn
        obtain ⟨tail, selected, tupleEq⟩ := List.mem_map.mp tailIn
        obtain ⟨headEq, tailEq⟩ := List.cons.inj tupleEq
        exact List.mem_flatMap.mpr ⟨first, headEq ▸ chosenIn, List.mem_map.mpr
          ⟨others, by simpa only [headEq, tailEq] using selected, same⟩⟩

/-- Every output arity comes from an actual row of a key owner. -/
theorem rows_arity (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (output : Row (List State) Symbol (List (List Nat)))
    (present : output ∈ rows lookup key) :
    ∃ owner ∈ key, ∃ original ∈ lookup owner, output.children.length = original.children.length := by
  obtain ⟨first, others, tupleIn, rfl⟩ := (mem_rows lookup key output).mp present
  obtain ⟨owner, ownerIn, stored⟩ := SourceSizedConjunctionTuples.row_origin lookup key _ tupleIn first (by simp)
  exact ⟨owner, ownerIn, first, stored, intersection_arity first others⟩

/-- Actual same-token tuple selection derives nonempty child keys for every row. -/
theorem rows_nonempty (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (output : Row (List State) Symbol (List (List Nat)))
    (present : output ∈ rows lookup key) : ∀ child ∈ output.children, child ≠ [] := by
  obtain ⟨first, others, tupleIn, rfl⟩ := (mem_rows lookup key output).mp present
  apply intersection_nonempty
  intro member memberIn
  exact (SourceSizedConjunctionTuples.common_shape lookup key _ tupleIn member first memberIn (by simp)).2

/-- Computed rows derive their local conjunction law from classified input bounds. -/
theorem rows_exact (lookup : State → List (Row State Symbol (List (List Nat))))
    (valid : ∀ owner row, row ∈ lookup owner → CompactGroups.ValidClasses row.children.length row.constraint)
    (key : List State) (output : Row (List State) Symbol (List (List Nat)))
    (present : output ∈ rows lookup key) (domain : State → Value → Prop) (value : Nat → Value) :
    ∃ first others, first :: others ∈ SourceSizedConjunctionTuples.tuples lookup key ∧
      output = intersection first others ∧
      (assignmentHolds output (fun child selected => ∀ state ∈ child, domain state selected) value ↔
        ∀ member ∈ first :: others, assignmentHolds member domain value) := by
  obtain ⟨first, others, tupleIn, rfl⟩ := (mem_rows lookup key output).mp present
  have arities : ∀ member ∈ first :: others, member.children.length = first.children.length := by
    intro member memberIn
    exact (SourceSizedConjunctionTuples.common_shape lookup key _ tupleIn member first memberIn (by simp)).2
  refine ⟨first, others, tupleIn, rfl, intersection_exact first others arities ?_ domain value⟩
  intro positions positionsIn index indexIn
  obtain ⟨member, memberIn, classIn⟩ := List.mem_flatMap.mp positionsIn
  obtain ⟨owner, _, stored⟩ := SourceSizedConjunctionTuples.row_origin lookup key _ tupleIn member memberIn
  rw [← arities member memberIn]
  exact valid owner member stored positions classIn index indexIn

end MicroCFTA.SourceSizedConjunctionRows
