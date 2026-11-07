import MicroCFTA.SourceSizedConjunctionGroupKeys

/-!
# Position map of an equal-child intersection transition

The source writes one conjunction key at each position in each joined group.
The partition laws give every original position exactly once. Ascending map
readback therefore retains every assignment without an overwrite. This module
models that value readback. It does not prove native IntMap representation.
-/
namespace MicroCFTA.SourceSizedConjunctionPositions
open SourceSizedDecided SourceSizedConjunctionGroupKeys

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Emit the source group-major position assignments. -/
def assignments (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    List (Nat × List State) :=
  (CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint)).flatMap
    fun group => group.map fun position => (position, groupKey tuple group)

/-- Read the position map in ascending integer-key order. -/
def orderedAssignments (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    List (Nat × List State) :=
  (assignments tuple arity).mergeSort fun first second => decide (first.1 ≤ second.1)

/-- The source transition children are the ascending position-map values. -/
def children (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) : List (List State) :=
  (orderedAssignments tuple arity).map Prod.snd

/-- Assignment keys retain the complete source group partition. -/
theorem assignment_positions (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    (assignments tuple arity).map Prod.fst =
      (CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint)).flatten := by
  simp [assignments, List.map_flatMap, List.map_map, Function.comp_def]

/-- Every child position is assigned with its original multiplicity. -/
theorem positions_perm (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    ((assignments tuple arity).map Prod.fst).Perm (List.range arity) := by
  rw [assignment_positions]
  exact CompactGroups.childGroups_positions arity _

/-- No source position assignment overwrites another position. -/
theorem positions_nodup (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    ((assignments tuple arity).map Prod.fst).Nodup :=
  (positions_perm tuple arity).nodup_iff.mpr List.nodup_range

/-- Ascending map keys are exactly the original ordered child positions. -/
theorem ordered_positions (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    (orderedAssignments tuple arity).map Prod.fst = List.range arity := by
  have ordered : (orderedAssignments tuple arity).Pairwise
      (fun first second => first.1 ≤ second.1) := by
    unfold orderedAssignments
    have sorted := List.pairwise_mergeSort
      (le := fun first second : Nat × List State => decide (first.1 ≤ second.1))
      (by
        intro a b c ab bc
        simp only [decide_eq_true_eq] at *
        omega)
      (by
        intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega)
      (assignments tuple arity)
    simpa only [decide_eq_true_eq] using sorted
  apply List.Perm.eq_of_pairwise (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
    (List.pairwise_map.mpr ordered) (List.pairwise_lt_range.imp Nat.le_of_lt)
  exact ((List.mergeSort_perm (assignments tuple arity) _).map Prod.fst).trans
    (positions_perm tuple arity)

/-- Reading all position-map values preserves the original transition arity. -/
theorem children_length (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat) :
    (children tuple arity).length = arity := by
  have same := congrArg List.length (ordered_positions tuple arity)
  simpa only [children, List.length_map, List.length_range] using same

/-- Each assignment names its actual group and its assigned group key. -/
theorem mem_assignments (tuple : List (Row State Symbol (List (List Nat)))) (arity position : Nat)
    (key : List State) :
    (position, key) ∈ assignments tuple arity ↔
      ∃ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
        position ∈ group ∧ key = groupKey tuple group := by
  constructor
  · intro present
    obtain ⟨group, groupIn, member⟩ := List.mem_flatMap.mp present
    obtain ⟨index, indexIn, same⟩ := List.mem_map.mp member
    have indexEq : index = position := congrArg Prod.fst same
    exact ⟨group, groupIn, indexEq ▸ indexIn, (congrArg Prod.snd same).symm⟩
  · rintro ⟨group, groupIn, positionIn, same⟩
    subst key
    exact List.mem_flatMap.mpr ⟨group, groupIn, List.mem_map.mpr ⟨position, positionIn, rfl⟩⟩

/-- Every returned child key comes from a group with an assigned position. -/
theorem child_origin (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat)
    (key : List State) (present : key ∈ children tuple arity) :
    ∃ group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint),
      ∃ position ∈ group, key = groupKey tuple group := by
  obtain ⟨entry, entryIn, valueEq⟩ := List.mem_map.mp present
  have original := (List.mergeSort_perm (assignments tuple arity) _).mem_iff.mp entryIn
  obtain ⟨group, groupIn, positionIn, keyEq⟩ := (mem_assignments tuple arity entry.1 entry.2).mp original
  exact ⟨group, groupIn, entry.1, positionIn, valueEq ▸ keyEq⟩

/-- Each position reads the key computed from its entire joined group. -/
theorem child_at (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat)
    (group : List Nat)
    (groupIn : group ∈ CompactGroups.childGroups arity (tuple.flatMap fun member => member.constraint))
    (position : Nat) (positionIn : position ∈ group) :
    (children tuple arity)[position]? = some (groupKey tuple group) := by
  have entryIn : (position, groupKey tuple group) ∈ orderedAssignments tuple arity :=
    (List.mergeSort_perm (assignments tuple arity) _).mem_iff.mpr
      ((mem_assignments tuple arity position _).mpr ⟨group, groupIn, positionIn, rfl⟩)
  obtain ⟨index, within, atIndex⟩ := List.getElem_of_mem entryIn
  have lengthEq := congrArg List.length (ordered_positions tuple arity)
  simp only [List.length_map, List.length_range] at lengthEq
  have bounded : index < arity := by omega
  have keys := congrArg (fun values => values[index]?) (ordered_positions tuple arity)
  have atKey : some (orderedAssignments tuple arity)[index].1 = some index := by
    simpa [List.getElem?_map, List.getElem?_eq_getElem within, bounded] using keys
  have same : index = position :=
    (Option.some.inj atKey).symm.trans (congrArg Prod.fst atIndex)
  subst position
  unfold children
  rw [List.getElem?_map, List.getElem?_eq_getElem within, atIndex]
  rfl

/-- A nonempty common-arity tuple produces no empty reached child key. -/
theorem children_nonempty (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat)
    (nonempty : tuple ≠ []) (arities : ∀ member ∈ tuple, member.children.length = arity) :
    ∀ key ∈ children tuple arity, key ≠ [] := by
  intro key present
  obtain ⟨group, groupIn, position, positionIn, same⟩ := child_origin tuple arity key present
  rw [same]
  have valid : ∀ index ∈ group, index < arity := by
    intro index indexIn
    exact List.mem_range.mp ((CompactGroups.childGroups_positions arity _).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, groupIn, indexIn⟩))
  have groupNonempty : group ≠ [] := by
    intro empty
    rw [empty] at positionIn
    exact List.not_mem_nil positionIn
  exact groupKey_nonempty tuple group arity arities valid nonempty groupNonempty

/-- Returned child keys retain the original finite state-key support. -/
theorem children_supported (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (closed : SourceSizedFiniteKeys.Closed table)
    (tuple : List (Row State Symbol (List (List Nat)))) (arity : Nat)
    (stored : ∀ member ∈ tuple, ∃ owner original,
      original ∈ SourceSizedFiniteKeys.lookup table owner ∧ original.children = member.children) :
    ∀ key ∈ children tuple arity, ∀ state ∈ key, state ∈ SourceDenseRows.keys table := by
  intro key present state stateIn
  obtain ⟨group, _, _, _, same⟩ := child_origin tuple arity key present
  rw [same] at stateIn
  exact groupKey_supported table closed tuple stored group state stateIn

end MicroCFTA.SourceSizedConjunctionPositions
