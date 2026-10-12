import MicroCFTA.Language

/-!
# Direct-child equality groups in the compact automaton compiler

The source starts with singleton positions. For each equality class it joins
all groups that meet that class, then sorts by the first child position.
-/
namespace MicroCFTA.CompactGroups

/-- The source membership test for a group touched by an equality class. -/
def hits (positions group : List Nat) : Bool := group.any (fun index => positions.contains index)

/-- The touched groups in their current order. -/
def selected (positions : List Nat) (groups : List (List Nat)) : List (List Nat) :=
  groups.filter (hits positions)

/-- Untouched groups retain their current order before sorting. -/
def untouched (positions : List Nat) (groups : List (List Nat)) : List (List Nat) :=
  groups.filter (fun group => !hits positions group)

/-- The source sortOn (take 1) key comparison. -/
def firstLE (left right : List Nat) : Bool := compare (left.take 1) (right.take 1) != .gt

/-- Execute the source equality-class merge. -/
def merge (groups : List (List Nat)) (positions : List Nat) : List (List Nat) :=
  if positions.isEmpty then groups
  else ((selected positions groups).flatten :: untouched positions groups).mergeSort firstLE

/-- Every child index occurs exactly once before and after a merge. -/
theorem merge_positions (groups : List (List Nat)) (positions : List Nat) :
    (merge groups positions).flatten.Perm groups.flatten := by
  unfold merge
  split
  · exact .refl _
  · exact (List.mergeSort_perm _ firstLE).flatten.trans
      (by simpa [selected, untouched] using (List.filter_append_perm (hits positions) groups).flatten)

/-- Sorting changes neither the merged block nor the untouched blocks. -/
theorem merge_member (groups : List (List Nat)) (positions group : List Nat)
    (nonempty : positions ≠ []) :
    group ∈ merge groups positions ↔
      group = (selected positions groups).flatten ∨ group ∈ untouched positions groups := by
  simp [merge, List.isEmpty_eq_false_iff.mpr nonempty]

theorem hits_iff (positions group : List Nat) :
    hits positions group = true ↔ ∃ index, index ∈ group ∧ index ∈ positions := by
  simp [hits, List.any_eq_true]

/-- Every old group is contained in one resulting group. -/
theorem merge_refines (groups : List (List Nat)) (positions group : List Nat)
    (member : group ∈ groups) :
    ∃ result ∈ merge groups positions, ∀ index ∈ group, index ∈ result := by
  by_cases empty : positions = []
  · subst positions
    exact ⟨group, by simpa [merge] using member, fun _ present => present⟩
  · by_cases touched : hits positions group = true
    · refine ⟨(selected positions groups).flatten, (merge_member groups positions _ empty).mpr (Or.inl rfl), ?_⟩
      intro index present
      exact List.mem_flatten.mpr ⟨group, by simp [selected, member, touched], present⟩
    · refine ⟨group, (merge_member groups positions _ empty).mpr (Or.inr ?_), fun _ present => present⟩
      simp [untouched, member, touched]

/-- All positions read by a valid class occur in its merged group. -/
theorem class_in_selected (groups : List (List Nat)) (positions : List Nat)
    (covered : ∀ index ∈ positions, index ∈ groups.flatten) :
    ∀ index ∈ positions, index ∈ (selected positions groups).flatten := by
  intro index present
  obtain ⟨group, member, contains⟩ := List.mem_flatten.mp (covered index present)
  have touched := (hits_iff positions group).mpr ⟨index, contains, present⟩
  exact List.mem_flatten.mpr ⟨group, by simp [selected, member, touched], contains⟩

/-- A nonempty valid class always selects a nonempty block. -/
theorem selected_nonempty (groups : List (List Nat)) (positions : List Nat)
    (nonempty : positions ≠ []) (covered : ∀ index ∈ positions, index ∈ groups.flatten) :
    (selected positions groups).flatten ≠ [] := by
  obtain ⟨index, present⟩ := List.exists_mem_of_ne_nil positions nonempty
  have member := class_in_selected groups positions covered index present
  intro empty
  simp [empty] at member

/-- Valid merging cannot introduce an empty group. -/
theorem merge_nonempty (groups : List (List Nat)) (positions : List Nat)
    (before : ∀ group ∈ groups, group ≠ [])
    (covered : ∀ index ∈ positions, index ∈ groups.flatten) :
    ∀ group ∈ merge groups positions, group ≠ [] := by
  by_cases empty : positions = []
  · simpa [merge, empty] using before
  · intro group member
    rcases (merge_member groups positions group empty).mp member with same | retained
    · subst group
      exact selected_nonempty groups positions empty covered
    · exact before group (List.mem_filter.mp retained).1

/-- The values at one equality class must agree. -/
def EqualAt (value : Nat → Value) (positions : List Nat) : Prop :=
  ∀ left ∈ positions, ∀ right ∈ positions, value left = value right

/-- The values must agree inside each current group. -/
def GroupsEqual (value : Nat → Value) (groups : List (List Nat)) : Prop :=
  ∀ group ∈ groups, EqualAt value group

/-- A merged assignment still satisfies every previous group. -/
theorem merge_keeps_equal (value : Nat → Value) (groups : List (List Nat)) (positions : List Nat)
    (after : GroupsEqual value (merge groups positions)) : GroupsEqual value groups := by
  intro group member left leftMember right rightMember
  obtain ⟨result, retained, contains⟩ := merge_refines groups positions group member
  exact after result retained left (contains left leftMember) right (contains right rightMember)

/-- The new merged assignment enforces every equality from the processed class. -/
theorem merge_enforces (value : Nat → Value) (groups : List (List Nat)) (positions : List Nat)
    (covered : ∀ index ∈ positions, index ∈ groups.flatten)
    (after : GroupsEqual value (merge groups positions)) : EqualAt value positions := by
  by_cases empty : positions = []
  · simp [EqualAt, empty]
  · have member := (merge_member groups positions _ empty).mpr (Or.inl rfl)
    intro left leftMember right rightMember
    exact after _ member left (class_in_selected groups positions covered left leftMember)
      right (class_in_selected groups positions covered right rightMember)

/-- Joining touched groups adds only the requested equalities. -/
theorem merge_adds_only (value : Nat → Value) (groups : List (List Nat)) (positions : List Nat)
    (before : GroupsEqual value groups) (constraint : EqualAt value positions) :
    GroupsEqual value (merge groups positions) := by
  by_cases empty : positions = []
  · simpa [merge, empty] using before
  · intro group member
    rcases (merge_member groups positions group empty).mp member with same | retained
    · subst group
      intro left leftMember right rightMember
      obtain ⟨leftGroup, leftSelected, leftPresent⟩ := List.mem_flatten.mp leftMember
      obtain ⟨rightGroup, rightSelected, rightPresent⟩ := List.mem_flatten.mp rightMember
      obtain ⟨leftStored, leftHits⟩ := List.mem_filter.mp leftSelected
      obtain ⟨rightStored, rightHits⟩ := List.mem_filter.mp rightSelected
      obtain ⟨leftLink, leftInGroup, leftInClass⟩ := (hits_iff positions leftGroup).mp leftHits
      obtain ⟨rightLink, rightInGroup, rightInClass⟩ := (hits_iff positions rightGroup).mp rightHits
      exact (before leftGroup leftStored left leftPresent leftLink leftInGroup).trans
        ((constraint leftLink leftInClass rightLink rightInClass).trans
          (before rightGroup rightStored rightLink rightInGroup right rightPresent))
    · exact before group (List.mem_filter.mp retained).1

/-- One source merge enforces exactly the old groups and the current class. -/
theorem merge_exact (value : Nat → Value) (groups : List (List Nat)) (positions : List Nat)
    (covered : ∀ index ∈ positions, index ∈ groups.flatten) :
    GroupsEqual value (merge groups positions) ↔ GroupsEqual value groups ∧ EqualAt value positions :=
  ⟨fun after => ⟨merge_keeps_equal value groups positions after, merge_enforces value groups positions covered after⟩,
    fun before => merge_adds_only value groups positions before.1 before.2⟩

/-- The full source fold keeps every position with its original multiplicity. -/
theorem fold_positions (classes groups : List (List Nat)) :
    (classes.foldl merge groups).flatten.Perm groups.flatten := by
  induction classes generalizing groups with
  | nil => exact .refl _
  | cons positions rest ih =>
      exact (ih (merge groups positions)).trans (merge_positions groups positions)

/-- Each completed fold enforces exactly the input classes and initial groups. -/
theorem fold_exact (value : Nat → Value) (classes groups : List (List Nat))
    (covered : ∀ positions ∈ classes, ∀ index ∈ positions, index ∈ groups.flatten) :
    GroupsEqual value (classes.foldl merge groups) ↔
      GroupsEqual value groups ∧ ∀ positions ∈ classes, EqualAt value positions := by
  induction classes generalizing groups with
  | nil => simp [GroupsEqual]
  | cons positions rest ih =>
      have head := covered positions (by simp)
      have later : ∀ next ∈ rest, ∀ index ∈ next, index ∈ (merge groups positions).flatten := by
        intro next member index present
        exact (merge_positions groups positions).mem_iff.mpr (covered next (by simp [member]) index present)
      rw [List.foldl_cons, ih (merge groups positions) later, merge_exact value groups positions head]
      simp only [List.forall_mem_cons, and_assoc]

/-- Valid classes also keep every group nonempty through the source fold. -/
theorem fold_nonempty (classes groups : List (List Nat))
    (before : ∀ group ∈ groups, group ≠ [])
    (covered : ∀ positions ∈ classes, ∀ index ∈ positions, index ∈ groups.flatten) :
    ∀ group ∈ classes.foldl merge groups, group ≠ [] := by
  induction classes generalizing groups with
  | nil => exact before
  | cons positions rest ih =>
      apply ih (merge groups positions) (merge_nonempty groups positions before (covered positions (by simp)))
      intro next member index present
      exact (merge_positions groups positions).mem_iff.mpr (covered next (by simp [member]) index present)

/-- Every direct child starts in its own singleton group. -/
def childGroups (arity : Nat) (classes : List (List Nat)) : List (List Nat) :=
  classes.foldl merge ((List.range arity).map (fun index => [index]))

/-- The initial singleton partition has the original ordered positions. -/
theorem singleton_flatten (positions : List Nat) :
    (positions.map (fun index => [index])).flatten = positions := by
  induction positions with
  | nil => rfl
  | cons first rest ih => simp [ih]

/-- The checked path parser ensures all class members are valid direct-child indexes. -/
def ValidClasses (arity : Nat) (classes : List (List Nat)) : Prop :=
  ∀ positions ∈ classes, ∀ index ∈ positions, index < arity

/-- Source childGroups covers every child exactly once. -/
theorem childGroups_positions (arity : Nat) (classes : List (List Nat)) :
    (childGroups arity classes).flatten.Perm (List.range arity) := by
  simpa [childGroups, singleton_flatten] using fold_positions classes ((List.range arity).map (fun index => [index]))

theorem childGroups_nodup (arity : Nat) (classes : List (List Nat)) :
    (childGroups arity classes).flatten.Nodup :=
  (childGroups_positions arity classes).nodup_iff.mpr List.nodup_range

/-- A valid normalized class cannot produce the empty buildGroup failure. -/
theorem childGroups_nonempty (arity : Nat) (classes : List (List Nat)) (valid : ValidClasses arity classes) :
    ∀ group ∈ childGroups arity classes, group ≠ [] := by
  apply fold_nonempty
  · intro group member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    subst group
    simp
  · intro positions member index present
    simpa [singleton_flatten] using valid positions member index present

/-- The source grouping enforces exactly the parsed direct-child equalities. -/
theorem childGroups_exact (value : Nat → Value) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) :
    GroupsEqual value (childGroups arity classes) ↔ ∀ positions ∈ classes, EqualAt value positions := by
  unfold childGroups
  rw [fold_exact value classes _ (by
    intro positions member index present
    simpa [singleton_flatten] using valid positions member index present)]
  simp [GroupsEqual, EqualAt]

/-- One selected term must belong to every child domain in its group. -/
def GroupSelection (domain : Nat → Value → Prop) (value : Nat → Value) (group : List Nat) : Prop :=
  ∃ selected, ∀ index ∈ group, domain index selected ∧ value index = selected

/-- Group intersection and duplication describe exactly all valid child assignments. -/
theorem groupSelections_exact (domain : Nat → Value → Prop) (value : Nat → Value)
    (arity : Nat) (classes : List (List Nat)) (valid : ValidClasses arity classes) :
    (∀ group ∈ childGroups arity classes, GroupSelection domain value group) ↔
      (∀ index, index < arity → domain index (value index)) ∧
        ∀ positions ∈ classes, EqualAt value positions := by
  constructor
  · intro selected
    constructor
    · intro index within
      have present := (childGroups_positions arity classes).mem_iff.mpr (List.mem_range.mpr within)
      obtain ⟨group, member, contains⟩ := List.mem_flatten.mp present
      obtain ⟨term, facts⟩ := selected group member
      obtain ⟨accepted, same⟩ := facts index contains
      simpa [same] using accepted
    · apply (childGroups_exact value arity classes valid).mp
      intro group member left leftMember right rightMember
      obtain ⟨term, facts⟩ := selected group member
      exact (facts left leftMember).2.trans (facts right rightMember).2.symm
  · rintro ⟨accepted, equalities⟩ group member
    obtain ⟨index, present⟩ := List.exists_mem_of_ne_nil group (childGroups_nonempty arity classes valid group member)
    have equal := (childGroups_exact value arity classes valid).mpr equalities group member
    refine ⟨value index, ?_⟩
    intro other otherMember
    have within : other < arity := List.mem_range.mp
      ((childGroups_positions arity classes).mem_iff.mp (List.mem_flatten.mpr ⟨group, member, otherMember⟩))
    have same := equal other otherMember index present
    exact ⟨by simpa [same] using accepted other within, same⟩

/-- The source accepts one signed direct-child index inside the declared arity. -/
def childIndex (arity : Nat) : List Int → Option Nat
  | [index] => if 0 ≤ index ∧ index < (arity : Int) then some index.toNat else none
  | _ => none

/-- Successful path parsing retains the exact original index and its bounds. -/
theorem childIndex_exact (arity index : Nat) (path : List Int) :
    childIndex arity path = some index ↔ path = [(index : Int)] ∧ index < arity := by
  cases path with
  | nil => simp [childIndex]
  | cons first rest => cases rest with
    | cons second rest => simp [childIndex]
    | nil =>
        simp only [childIndex]
        split
        · rename_i valid
          simp only [Option.some.injEq, List.cons.injEq, and_true]
          constructor
          · intro same
            constructor <;> omega
          · rintro ⟨same, _⟩
            omega
        · rename_i invalid
          constructor
          · simp
          · rintro ⟨same, bound⟩
            have equal : first = (index : Int) := List.cons.inj same |>.1
            omega

/-- Source traverse over one normalized equality class. -/
def parseClass (arity : Nat) : List (List Int) → Option (List Nat)
  | [] => some []
  | path :: rest => do
      let index ← childIndex arity path
      let indexes ← parseClass arity rest
      pure (index :: indexes)

/-- Parsing preserves every class position in its original order. -/
theorem parseClass_exact (arity : Nat) (paths : List (List Int)) (positions : List Nat) :
    parseClass arity paths = some positions ↔
      paths = positions.map (fun (index : Nat) => [(index : Int)]) ∧ ∀ index ∈ positions, index < arity := by
  induction paths generalizing positions with
  | nil => cases positions <;> simp [parseClass]
  | cons path rest ih =>
      cases positions with
      | nil =>
          simp only [List.map_nil, reduceCtorEq, false_and, parseClass]
          cases childIndex arity path <;> cases parseClass arity rest <;> simp
      | cons first later =>
          simp only [parseClass, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq, List.cons.injEq]
          constructor
          · rintro ⟨index, parsed, indexes, remaining, same, tail⟩
            subst index
            subst indexes
            have head := (childIndex_exact arity first path).mp parsed
            have rest := (ih later).mp remaining
            exact ⟨by simp [head.1, rest.1], by simpa using And.intro head.2 rest.2⟩
          · rintro ⟨shape, bounds⟩
            have heads := List.cons.inj shape
            refine ⟨first, (childIndex_exact arity first path).mpr ⟨heads.1, bounds first (by simp)⟩,
              later, (ih later).mpr ⟨heads.2, fun index member => bounds index (by simp [member])⟩, rfl, rfl⟩

/-- Source traverse over all normalized equality classes. -/
def parseClasses (arity : Nat) : List (List (List Int)) → Option (List (List Nat))
  | [] => some []
  | paths :: rest => do
      let positions ← parseClass arity paths
      let classes ← parseClasses arity rest
      pure (positions :: classes)

/-- Actual successful parsing supplies every class-range premise used above. -/
theorem parseClasses_valid (arity : Nat) (paths : List (List (List Int)))
    (classes : List (List Nat)) (success : parseClasses arity paths = some classes) :
    ValidClasses arity classes := by
  induction paths generalizing classes with
  | nil =>
      have empty : classes = [] := by simpa [parseClasses] using success.symm
      simp [ValidClasses, empty]
  | cons first rest ih =>
      simp only [parseClasses, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at success
      obtain ⟨positions, parsed, remaining, later, same⟩ := success
      subst classes
      intro group member
      rcases List.mem_cons.mp member with same | member
      · subst group
        exact (parseClass_exact arity first positions).mp parsed |>.2
      · exact ih remaining later group member

/-- A successful compact child parser gives the complete group-selection equivalence. -/
theorem compiled_groups_exact (domain : Nat → Value → Prop) (value : Nat → Value)
    (arity : Nat) (paths : List (List (List Int))) (classes : List (List Nat))
    (success : parseClasses arity paths = some classes) :
    (∀ group ∈ childGroups arity classes, GroupSelection domain value group) ↔
      (∀ index, index < arity → domain index (value index)) ∧
        ∀ positions ∈ classes, EqualAt value positions :=
  groupSelections_exact domain value arity classes (parseClasses_valid arity paths classes success)

example : childGroups 5 [[0, 2], [2, 4]] = [[0, 2, 4], [1], [3]] := by cbv
example : parseClasses 3 [[[-1]]] = none := by decide
example : parseClasses 3 [[[3]]] = none := by decide
example : parseClasses 3 [[[0, 1]]] = none := by decide
example : childGroups 0 [] = [] := rfl

end MicroCFTA.CompactGroups
