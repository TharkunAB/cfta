import MicroCFTA.CompactGroups
import MicroCFTA.CanonicalClasses
import MicroCFTA.SourceSizedFiniteKeys

/-!
# Conjunction keys for equal-child intersection tuples

Each key contains every child read at a group position in every tuple row.
Valid positions and a common arity make each read total. Joined groups select
one value that satisfies every stored child domain and every input equality.
These laws do not assume a completed exploration or define its worker.
-/
namespace MicroCFTA.SourceSizedConjunctionGroupKeys
open SourceSizedDecided

variable {State Symbol Value Payload : Type}

/-- Read every group position in every row, then form the source set key. -/
def groupKey [DecidableEq State] [Ord State]
    (tuple : List (Row State Symbol (List (List Nat)))) (group : List Nat) : List State :=
  CanonicalClasses.sortedSet
    (tuple.flatMap fun member => group.filterMap fun index => member.children[index]?)

/-- A position must satisfy each tuple row that has a child at that position. -/
def domainAt (tuple : List (Row State Symbol (List (List Nat))))
    (domain : State → Value → Prop) (index : Nat) (value : Value) : Prop :=
  ∀ member ∈ tuple, ∀ state, member.children[index]? = some state → domain state value

section Keys
variable [DecidableEq State] [Ord State]

/-- Key membership retains both the source tuple row and the group position. -/
theorem mem_groupKey (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) (state : State) :
    state ∈ groupKey tuple group ↔
      ∃ member ∈ tuple, ∃ index ∈ group, member.children[index]? = some state := by
  rw [groupKey, CanonicalClasses.mem_sortedSet]
  constructor
  · intro present
    obtain ⟨member, memberIn, read⟩ := List.mem_flatMap.mp present
    obtain ⟨index, indexIn, found⟩ := List.mem_filterMap.mp read
    exact ⟨member, memberIn, index, indexIn, found⟩
  · rintro ⟨member, memberIn, index, indexIn, found⟩
    exact List.mem_flatMap.mpr
      ⟨member, memberIn, List.mem_filterMap.mpr ⟨index, indexIn, found⟩⟩

/-- The set key has no repeated state. -/
theorem groupKey_nodup (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) : (groupKey tuple group).Nodup :=
  CanonicalClasses.sortedSet_nodup _

/-- Common arity and valid positions cover every source partial child read. -/
theorem reads_total (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) (arity : Nat)
    (arities : ∀ member ∈ tuple, member.children.length = arity)
    (valid : ∀ index ∈ group, index < arity) :
    ∀ member ∈ tuple, ∀ index ∈ group,
      ∃ state, member.children[index]? = some state ∧ state ∈ groupKey tuple group := by
  intro member memberIn index indexIn
  have within : index < member.children.length := by
    rw [arities member memberIn]
    exact valid index indexIn
  have found : member.children[index]? = some member.children[index] :=
    List.getElem?_eq_getElem within
  exact ⟨member.children[index], found,
    (mem_groupKey tuple group _).mpr ⟨member, memberIn, index, indexIn, found⟩⟩

/-- Nonempty tuples and valid nonempty groups cannot produce an empty key. -/
theorem groupKey_nonempty (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) (arity : Nat)
    (arities : ∀ member ∈ tuple, member.children.length = arity)
    (valid : ∀ index ∈ group, index < arity)
    (tupleNonempty : tuple ≠ []) (groupNonempty : group ≠ []) :
    groupKey tuple group ≠ [] := by
  obtain ⟨member, memberIn⟩ := List.exists_mem_of_ne_nil tuple tupleNonempty
  obtain ⟨index, indexIn⟩ := List.exists_mem_of_ne_nil group groupNonempty
  obtain ⟨state, _, stateIn⟩ :=
    reads_total tuple group arity arities valid member memberIn index indexIn
  intro empty
  rw [empty] at stateIn
  exact List.not_mem_nil stateIn

/-- A key denotes the conjunction over all tuple rows and all group positions. -/
theorem key_language (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) (domain : State → Value → Prop) (selected : Value) :
    (∀ state ∈ groupKey tuple group, domain state selected) ↔
      ∀ index ∈ group, domainAt tuple domain index selected := by
  constructor
  · intro accepted index indexIn member memberIn state found
    exact accepted state
      ((mem_groupKey tuple group state).mpr ⟨member, memberIn, index, indexIn, found⟩)
  · intro accepted state stateIn
    obtain ⟨member, memberIn, index, indexIn, found⟩ :=
      (mem_groupKey tuple group state).mp stateIn
    exact accepted index indexIn member memberIn state found

/-- One key value and repeated positions are precisely one joined-group selection. -/
theorem selection_iff (tuple : List (Row State Symbol (List (List Nat))))
    (group : List Nat) (domain : State → Value → Prop) (value : Nat → Value) :
    (∃ selected, (∀ state ∈ groupKey tuple group, domain state selected) ∧
      ∀ index ∈ group, value index = selected) ↔
      CompactGroups.GroupSelection (domainAt tuple domain) value group := by
  constructor
  · rintro ⟨selected, accepted, repeated⟩
    refine ⟨selected, ?_⟩
    intro index indexIn
    exact ⟨(key_language tuple group domain selected).mp accepted index indexIn,
      repeated index indexIn⟩
  · rintro ⟨selected, accepted⟩
    refine ⟨selected, (key_language tuple group domain selected).mpr ?_, ?_⟩
    · intro index indexIn
      exact (accepted index indexIn).1
    · intro index indexIn
      exact (accepted index indexIn).2

/-- Joined selections enforce every tuple child domain and every tuple equality. -/
theorem groupSelections_exact (tuple : List (Row State Symbol (List (List Nat))))
    (domain : State → Value → Prop) (value : Nat → Value) (arity : Nat)
    (arities : ∀ member ∈ tuple, member.children.length = arity)
    (valid : CompactGroups.ValidClasses arity (tuple.flatMap fun member => member.constraint)) :
    (∀ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
      ∃ selected, (∀ state ∈ groupKey tuple group, domain state selected) ∧
        ∀ index ∈ group, value index = selected) ↔
    (∀ member ∈ tuple, ∀ index (within : index < member.children.length),
      domain member.children[index] (value index)) ∧
    ∀ member ∈ tuple, ∀ positions ∈ member.constraint, CompactGroups.EqualAt value positions := by
  have selections :
      (∀ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
        ∃ selected, (∀ state ∈ groupKey tuple group, domain state selected) ∧
          ∀ index ∈ group, value index = selected) ↔
      ∀ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
        CompactGroups.GroupSelection (domainAt tuple domain) value group := by
    constructor
    · intro accepted group groupIn
      exact (selection_iff tuple group domain value).mp (accepted group groupIn)
    · intro accepted group groupIn
      exact (selection_iff tuple group domain value).mpr (accepted group groupIn)
  rw [selections, CompactGroups.groupSelections_exact (domainAt tuple domain) value arity _ valid]
  constructor
  · rintro ⟨accepted, equalities⟩
    constructor
    · intro member memberIn index within
      have validIndex : index < arity := by
        rw [← arities member memberIn]
        exact within
      exact accepted index validIndex member memberIn member.children[index]
        (List.getElem?_eq_getElem within)
    · intro member memberIn positions positionsIn
      exact equalities positions (List.mem_flatMap.mpr ⟨member, memberIn, positionsIn⟩)
  · rintro ⟨accepted, equalities⟩
    constructor
    · intro index validIndex member memberIn state found
      have within : index < member.children.length := by
        rw [arities member memberIn]
        exact validIndex
      have actual : member.children[index] = state :=
        Option.some.inj ((List.getElem?_eq_getElem within).symm.trans found)
      simpa only [actual] using accepted member memberIn index within
    · intro positions positionsIn
      obtain ⟨member, memberIn, present⟩ := List.mem_flatMap.mp positionsIn
      exact equalities member memberIn positions present

/-- Stored tuple rows retain original-key support after their constraints change. -/
theorem groupKey_supported (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (closed : SourceSizedFiniteKeys.Closed table)
    (tuple : List (Row State Symbol (List (List Nat))))
    (stored : ∀ member ∈ tuple, ∃ owner original,
      original ∈ SourceSizedFiniteKeys.lookup table owner ∧ original.children = member.children)
    (group : List Nat) (state : State) (present : state ∈ groupKey tuple group) :
    state ∈ SourceDenseRows.keys table := by
  obtain ⟨member, memberIn, index, _, found⟩ := (mem_groupKey tuple group state).mp present
  obtain ⟨owner, original, originalIn, childrenEq⟩ := stored member memberIn
  apply closed owner original originalIn state
  rw [childrenEq]
  exact List.mem_of_getElem? found

end Keys
end MicroCFTA.SourceSizedConjunctionGroupKeys
