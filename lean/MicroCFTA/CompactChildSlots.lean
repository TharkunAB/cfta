import MicroCFTA.CompactGroups
import MicroCFTA.ChildBuilder

/-!
# Actual child-slot construction after compact equality grouping

The source prepends every selected group's indexed terms to the earlier
association list. The final group order is reversed. Term.fromAssocs restores
child order. Its complete-index contract follows from the proved grouping.
-/
namespace MicroCFTA.CompactChildSlots
open CompactGroups

/-- One source addGroup step duplicates the selected term at all group positions. -/
def addGroup (entries : List (Nat × Value)) (group : List Nat × Value) : List (Nat × Value) :=
  group.1.foldr (fun index rest => (index, group.2) :: rest) entries

/-- Execute the actual source left fold over selected groups. -/
def slots (selected : List (List Nat × Value)) : List (Nat × Value) :=
  selected.foldl addGroup []

/-- The output value at each position agrees with that group's selected value. -/
def Agrees (value : Nat → Value) (selected : List (List Nat × Value)) : Prop :=
  ∀ group ∈ selected, ∀ index ∈ group.1, value index = group.2

theorem addGroup_append (entries : List (Nat × Value)) (group : List Nat × Value) :
    addGroup entries group = group.1.map (fun index => (index, group.2)) ++ entries := by
  rcases group with ⟨positions, value⟩
  induction positions with
  | nil => rfl
  | cons first rest ih => simp [addGroup]

/-- The accumulator fold reverses group order but retains every indexed value. -/
theorem fold_slots (selected : List (List Nat × Value)) (entries : List (Nat × Value)) :
    selected.foldl addGroup entries =
      selected.reverse.flatMap (fun group => group.1.map (fun index => (index, group.2))) ++ entries := by
  induction selected generalizing entries with
  | nil => rfl
  | cons first rest ih =>
      simp [List.foldl_cons, ih, addGroup_append, List.reverse_cons, List.flatMap_append, List.append_assoc]

/-- Every emitted association has exactly the selected group value. -/
theorem slots_values (value : Nat → Value) (selected : List (List Nat × Value))
    (agrees : Agrees value selected) :
    slots selected = ((selected.map Prod.fst).reverse.flatten).map (fun index => (index, value index)) := by
  rw [slots, fold_slots]
  simp only [List.append_nil, ← List.map_reverse, List.flatMap, List.map_flatten, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro group member
  apply List.map_congr_left
  intro index present
  rw [agrees group (List.mem_reverse.mp member) index present]

/-- Group order reversal does not alter the position multiset. -/
theorem reversed_positions (arity : Nat) (classes : List (List Nat)) :
    (childGroups arity classes).reverse.flatten.Perm (List.range arity) :=
  (List.reverse_perm _).flatten.trans (childGroups_positions arity classes)

/-- The generated associations are a permutation of the complete indexed child values. -/
theorem slots_permutation (value : Nat → Value) (selected : List (List Nat × Value))
    (arity : Nat) (classes : List (List Nat))
    (groups : selected.map Prod.fst = childGroups arity classes) (agrees : Agrees value selected) :
    (slots selected).Perm ((List.range arity).map (fun index => (index, value index))) := by
  rw [slots_values value selected agrees, groups]
  exact (reversed_positions arity classes).map _

/-- The numbered input list agrees with direct range-index construction. -/
theorem indexed_values (value : Nat → Value) (arity : Nat) :
    ChildBuilder.indexed ((List.range arity).map value) =
      (List.range arity).map (fun index => (index, value index)) := by
  apply List.ext_getElem?
  intro index
  by_cases within : index < arity
  · simp [ChildBuilder.indexed, within]
  · have outside : arity ≤ index := by omega
    simp [ChildBuilder.indexed, outside]

/-- All specialized and generic source builders receive complete child associations. -/
theorem fromAssocs_exact (symbol : Symbol) (value : Nat → TermRepresentation.Packed Symbol)
    (selected : List (List Nat × TermRepresentation.Packed Symbol)) (arity : Nat)
    (classes : List (List Nat)) (groups : selected.map Prod.fst = childGroups arity classes)
    (agrees : Agrees value selected) :
    ChildBuilder.fromAssocs symbol arity (slots selected) =
      some (TermRepresentation.node symbol ((List.range arity).map value)) := by
  have permutation := slots_permutation value selected arity classes groups agrees
  rw [← indexed_values value arity] at permutation
  simpa using ChildBuilder.fromAssocs_correct symbol ((List.range arity).map value) (slots selected) permutation

/-- Every selected group can be recovered from any one of its nonempty child positions. -/
theorem selection_unique (value : Nat → Value) (group : List Nat) (first second : Value)
    (nonempty : group ≠ [])
    (firstAgrees : ∀ index ∈ group, value index = first)
    (secondAgrees : ∀ index ∈ group, value index = second) : first = second := by
  obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil group nonempty
  exact (firstAgrees index member).symm.trans (secondAgrees index member)

/-- Parsed groups cannot identify two different selected terms through slot duplication. -/
theorem child_selection_unique (value : Nat → Value) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (group : List Nat) (member : group ∈ childGroups arity classes)
    (first second : Value) (firstAgrees : ∀ index ∈ group, value index = first)
    (secondAgrees : ∀ index ∈ group, value index = second) : first = second :=
  selection_unique value group first second (childGroups_nonempty arity classes valid group member) firstAgrees secondAgrees

/-- Source rankEdge scans the children in index order and keeps this group's positions. -/
def readGroup (values : List Value) (positions : List Nat) : List Value :=
  ((ChildBuilder.indexed values).filter (fun entry => positions.contains entry.1)).map Prod.snd

/-- The source scan reads exactly the requested existing child slots. -/
theorem readGroup_member (values : List Value) (positions : List Nat) (value : Value) :
    value ∈ readGroup values positions ↔
      ∃ index ∈ positions, values[index]? = some value := by
  simp only [readGroup, List.mem_map, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨index, found⟩, ⟨stored, member⟩, same⟩
    change found = value at same
    subst found
    exact ⟨index, member, (ChildBuilder.indexed_describes values index value).mp stored⟩
  · rintro ⟨index, member, found⟩
    exact ⟨(index, value), ⟨(ChildBuilder.indexed_describes values index value).mpr found, member⟩, rfl⟩

/-- The exact source head-and-all-equal check used before a group rank query. -/
def selectedGroup [DecidableEq Value] (values : List Value) (positions : List Nat) : Option Value :=
  match readGroup values positions with
  | [] => none
  | first :: rest => if rest.all (fun value => decide (value = first)) then some first else none

/-- Complete constant-valued groups survive the source inverse reader. -/
theorem selectedGroup_exact [DecidableEq Value] (values : List Value) (positions : List Nat)
    (selected : Value) (nonempty : positions ≠ [])
    (agrees : ∀ index ∈ positions, values[index]? = some selected) :
    selectedGroup values positions = some selected := by
  have allSame : ∀ value ∈ readGroup values positions, value = selected := by
    intro value member
    obtain ⟨index, present, found⟩ := (readGroup_member values positions value).mp member
    exact Option.some.inj (found.symm.trans (agrees index present))
  have present : selected ∈ readGroup values positions := by
    obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil positions nonempty
    exact (readGroup_member values positions selected).mpr ⟨index, member, agrees index member⟩
  cases found : readGroup values positions with
  | nil => simp [found] at present
  | cons first rest =>
      have same := allSame first (by simp [found])
      have later : ∀ value ∈ rest, value = first := fun value member =>
        (allSame value (by simp [found, member])).trans same.symm
      have checked : rest.all (fun value => decide (value = first)) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        exact later
      simp only [selectedGroup, found]
      rw [ite_eq_left checked]
      exact congrArg some same

/-- Every parsed group reads back the exact term duplicated by its decoder. -/
theorem childGroup_read [DecidableEq Value] (value : Nat → Value) (arity : Nat)
    (classes : List (List Nat)) (valid : ValidClasses arity classes)
    (group : List Nat) (member : group ∈ childGroups arity classes) (selected : Value)
    (agrees : ∀ index ∈ group, value index = selected) :
    selectedGroup ((List.range arity).map value) group = some selected := by
  apply selectedGroup_exact _ _ selected (childGroups_nonempty arity classes valid group member)
  intro index present
  have within : index < arity := List.mem_range.mp
    ((childGroups_positions arity classes).mem_iff.mp (List.mem_flatten.mpr ⟨group, member, present⟩))
  simp [within, agrees index present]

example : slots [([0, 2], 7), ([1], 8)] = [(1, 8), (0, 7), (2, 7)] := by decide
example : selectedGroup [7, 8, 7] [0, 2] = some 7 := by decide
example : selectedGroup [7, 8, 9] [0, 2] = none := by decide

end MicroCFTA.CompactChildSlots
