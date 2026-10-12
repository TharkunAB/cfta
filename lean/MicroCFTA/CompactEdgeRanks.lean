import MicroCFTA.CompactChildSlots
import MicroCFTA.Probability
import MicroCFTA.AutomatonAmbiguity

/-!
# Compact edge ranks and group reconstruction

The decoder folds the source applicative addGroup operation. Each step uses
one child index and a mixed-radix split. The inverse reads the actual grouped
child slots and folds the same radix. Child indexes are local induction inputs.
-/
namespace MicroCFTA.CompactEdgeRanks
open Language Probability CompactGroups CompactChildSlots

/-- Induct over the actual source left fold by appending its last group. -/
theorem snoc_induction {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ items last, motive items → motive (items ++ [last])) (items : List α) : motive items := by
  have reversed : ∀ rest : List α, motive rest.reverse := by
    intro rest
    induction rest with
    | nil => exact nil
    | cons first rest ih => simpa using snoc rest.reverse first ih
  simpa using reversed items.reverse

/-- A compiled child intersection has a finite count, direct selector, and inverse. -/
structure Index (Value : Type) where
  count : Nat
  select : Nat → Option Value
  rank : Value → Option Nat

/-- The local recursive compiler obligation for one child intersection. -/
structure Correct (index : Index Value) : Prop where
  bounded : ∀ rank value, index.select rank = some value → rank < index.count
  total : ∀ rank, rank < index.count → ∃ value, index.select rank = some value
  inverse : ∀ rank value, index.rank value = some rank ↔ index.select rank = some value

/-- One compact equality group and its compiled intersection index. -/
structure Group (Value : Type) where
  positions : List Nat
  index : Index Value

/-- The selection plan keeps only the count and the direct decoder. -/
structure Plan (Value : Type) where
  count : Nat
  select : Nat → Option (List (List Nat × Value))

/-- Source pure [] has one rank, including the nullary edge case. -/
def unitPlan : Plan Value := ⟨1, fun rank => if rank = 0 then some [] else none⟩

/-- One source prefix applicative product, before its association lists are assembled. -/
def addGroupPlan (initial : Plan Value) (group : Group Value) : Plan Value :=
  ⟨initial.count * group.index.count, fun rank =>
    if rank < initial.count * group.index.count then do
      let earlier ← initial.select (rank / group.index.count)
      let value ← group.index.select (rank % group.index.count)
      pure (earlier ++ [(group.positions, value)])
    else none⟩

/-- Actual source left fold over the compiled groups. -/
def plan (groups : List (Group Value)) : Plan Value := groups.foldl addGroupPlan unitPlan

/-- Appending a group adds exactly one source mixed-radix product. -/
theorem plan_snoc (groups : List (Group Value)) (last : Group Value) :
    plan (groups ++ [last]) = addGroupPlan (plan groups) last := by simp [plan]

/-- Deferring association construction until after selection gives the exact source addGroup fold. -/
theorem slots_snoc (selected : List (List Nat × Value)) (group : List Nat × Value) :
    slots (selected ++ [group]) = addGroup (slots selected) group := by simp [slots]

/-- A source decoder derivation records each selected group value and class rank. -/
inductive Decoded : List (Group Value) → List (List Nat × Value) → Nat → Prop where
  | nil : Decoded [] [] 0
  | snoc {groups selected rank} (previous : Decoded groups selected rank)
      (group : Group Value) (digit : Nat) (value : Value) (within : digit < group.index.count)
      (found : group.index.select digit = some value) :
      Decoded (groups ++ [group]) (selected ++ [(group.positions, value)])
        (pairRank group.index.count rank digit)

/-- Every group digit stays inside the complete mixed-radix count. -/
theorem decoded_bound {groups : List (Group Value)} {selected rank}
    (decoded : Decoded groups selected rank) : rank < (plan groups).count := by
  induction decoded with
  | nil => simp [plan, unitPlan]
  | snoc previous group digit value within found ih =>
      simpa [plan_snoc, addGroupPlan] using pairRank_lt ih within

/-- Decoder derivations preserve the exact source group order. -/
theorem decoded_groups {groups : List (Group Value)} {selected rank}
    (decoded : Decoded groups selected rank) : selected.map Prod.fst = groups.map Group.positions := by
  induction decoded with
  | nil => rfl
  | snoc previous group digit value within found ih => simp [ih]

/-- Every decoder derivation is returned by the actual left-fold plan. -/
theorem decoded_select {groups : List (Group Value)} {selected rank}
    (decoded : Decoded groups selected rank) : (plan groups).select rank = some selected := by
  induction decoded with
  | nil => rfl
  | @snoc groups selected rank previous group digit value within found ih =>
      have split := split_pair within (left := rank)
      have first := congrArg Prod.fst split
      have second := congrArg Prod.snd split
      simp only [splitRank] at first second
      have bounded := pairRank_lt (decoded_bound previous) within
      simp [plan_snoc, addGroupPlan, bounded, first, second, ih, found]

/-- The actual left-fold decoder yields a finite derivation of exactly its selected digits. -/
theorem select_decoded (groups : List (Group Value)) (rank : Nat) (selected : List (List Nat × Value))
    (found : (plan groups).select rank = some selected) : Decoded groups selected rank := by
  induction groups using snoc_induction generalizing rank selected with
  | nil =>
      simp only [plan, List.foldl_nil, unitPlan] at found
      split at found
      next zero => subst rank; cases found; exact .nil
      next => cases found
  | snoc groups group ih =>
      rw [plan_snoc] at found
      simp only [addGroupPlan] at found
      split at found
      next bounded =>
        obtain ⟨earlier, earlierFound, tail⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨value, valueFound, same⟩ := Option.bind_eq_some_iff.mp tail
        have sameSelected : earlier ++ [(group.positions, value)] = selected := Option.some.inj same
        subst selected
        have valid := split_lt bounded
        have result := Decoded.snoc (ih _ _ earlierFound) group (rank % group.index.count) value valid.2 valueFound
        have joined : pairRank group.index.count (rank / group.index.count) (rank % group.index.count) = rank :=
          pair_split group.index.count rank
        simpa only [joined] using result
      next => cases found

/-- Local total child indexes give a total edge product on its precise finite rank interval. -/
theorem plan_total (groups : List (Group Value)) (correct : ∀ group ∈ groups, Correct group.index)
    (rank : Nat) (within : rank < (plan groups).count) : ∃ selected, (plan groups).select rank = some selected := by
  induction groups using snoc_induction generalizing rank with
  | nil =>
      have zero : rank = 0 := by simpa [plan, unitPlan] using within
      exact ⟨[], by simp [plan, unitPlan, zero]⟩
  | snoc groups group ih =>
      have bounded : rank < (plan groups).count * group.index.count := by simpa [plan_snoc, addGroupPlan] using within
      have split := split_lt bounded
      obtain ⟨earlier, earlierFound⟩ := ih (fun g member => correct g (by simp [member])) _ split.1
      obtain ⟨value, found⟩ := (correct group (by simp)).total _ split.2
      simp only [splitRank] at earlierFound found
      exact ⟨earlier ++ [(group.positions, value)], by simp [plan_snoc, addGroupPlan, bounded, earlierFound, found]⟩

/-- No count metadata is supplied independently of the source product fold. -/
theorem plan_count (groups : List (Group Value)) :
    (plan groups).count = (groups.map (fun group => group.index.count)).prod := by
  induction groups using snoc_induction with
  | nil => rfl
  | snoc groups group ih => simp [plan_snoc, addGroupPlan, ih]

/-- The literal source inverse fold reads a group and appends its digit to the prefix rank. -/
def rankFold [DecidableEq Value] (values : List Value) : List (Group Value) → Nat → Option Nat
  | [], initial => some initial
  | group :: rest, initial => do
      let selected ← selectedGroup values group.positions
      let digit ← group.index.rank selected
      rankFold values rest (pairRank group.index.count initial digit)

/-- Source foldM over a final group has the actual prefix-first sequencing. -/
theorem rankFold_snoc [DecidableEq Value] (values : List Value) (groups : List (Group Value))
    (last : Group Value) (initial : Nat) :
    rankFold values (groups ++ [last]) initial = (do
      let earlier ← rankFold values groups initial
      let selected ← selectedGroup values last.positions
      let digit ← last.index.rank selected
      pure (pairRank last.index.count earlier digit)) := by
  induction groups generalizing initial with
  | nil => rfl
  | cons group rest ih => simp [rankFold, ih, Option.bind_assoc]

/-- Selected group values agree with the concrete child list at every assigned slot. -/
def SlotAgreement (values : List Value) (selected : List (List Nat × Value)) : Prop :=
  ∀ group ∈ selected, ∀ index ∈ group.1, values[index]? = some group.2

/-- The inverse reads each generated group digit and reconstructs the exact original product rank. -/
theorem rankFold_decoded [DecidableEq Value] {groups : List (Group Value)} {selected rank}
    (decoded : Decoded groups selected rank) (correct : ∀ group ∈ groups, Correct group.index)
    (nonempty : ∀ group ∈ groups, group.positions ≠ []) (values : List Value)
    (agrees : SlotAgreement values selected) : rankFold values groups 0 = some rank := by
  induction decoded with
  | nil => rfl
  | @snoc groups selected rank previous group digit value within found ih =>
      have prefixCorrect : ∀ g ∈ groups, Correct g.index := fun g member => correct g (by simp [member])
      have prefixNonempty : ∀ g ∈ groups, g.positions ≠ [] := fun g member => nonempty g (by simp [member])
      have prefixAgreement : SlotAgreement values selected := fun g member => agrees g (by simp [member])
      have prefixRank := ih prefixCorrect prefixNonempty prefixAgreement
      have read := selectedGroup_exact values group.positions value (nonempty group (by simp))
        (agrees (group.positions, value) (by simp))
      have inverse := (correct group (by simp)).inverse digit value |>.mpr found
      simp [rankFold_snoc, prefixRank, read, inverse]

/-- A successful source group reader has checked every child it read. -/
theorem selectedGroup_sound [DecidableEq Value] (values : List Value) (positions : List Nat) (selected : Value)
    (found : selectedGroup values positions = some selected) :
    ∀ value ∈ readGroup values positions, value = selected := by
  cases read : readGroup values positions with
  | nil => simp [selectedGroup, read] at found
  | cons first rest =>
      simp only [selectedGroup, read] at found
      split at found
      next checked =>
        have same : first = selected := Option.some.inj found
        intro value member
        rw [List.mem_cons] at member
        rcases member with rfl | member
        · exact same
        · have all := (List.all_eq_true.mp checked) value member
          exact (of_decide_eq_true all).trans same
      next => cases found

/-- In-range source group positions all read back the selected value. -/
theorem selectedGroup_slots [DecidableEq Value] (values : List Value) (positions : List Nat) (selected : Value)
    (found : selectedGroup values positions = some selected)
    (within : ∀ index ∈ positions, index < values.length) :
    ∀ index ∈ positions, values[index]? = some selected := by
  intro index member
  have bound := within index member
  have read : values[index] ∈ readGroup values positions :=
    (readGroup_member values positions _).mpr ⟨index, member, List.getElem?_eq_getElem bound⟩
  rw [List.getElem?_eq_getElem bound, selectedGroup_sound values positions selected found _ read]

/-- A successful source inverse fold has a decoder derivation and complete child-slot agreement. -/
theorem rankFold_sound [DecidableEq Value] (values : List Value) (groups : List (Group Value))
    (correct : ∀ group ∈ groups, Correct group.index)
    (within : ∀ group ∈ groups, ∀ index ∈ group.positions, index < values.length)
    (rank : Nat) (found : rankFold values groups 0 = some rank) :
    ∃ selected, Decoded groups selected rank ∧ SlotAgreement values selected := by
  induction groups using snoc_induction generalizing rank with
  | nil =>
      have zero : rank = 0 := (Option.some.inj found).symm
      subst rank
      exact ⟨[], .nil, by simp [SlotAgreement]⟩
  | snoc groups group ih =>
      rw [rankFold_snoc] at found
      obtain ⟨earlier, earlierFound, tail⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨value, read, tail⟩ := Option.bind_eq_some_iff.mp tail
      obtain ⟨digit, digitFound, same⟩ := Option.bind_eq_some_iff.mp tail
      have rankEq : pairRank group.index.count earlier digit = rank := Option.some.inj same
      obtain ⟨selected, previous, agrees⟩ := ih
        (fun g member => correct g (by simp [member]))
        (fun g member => within g (by simp [member])) earlier earlierFound
      have localCorrect := correct group (by simp)
      have selectedDigit := (localCorrect.inverse digit value).mp digitFound
      refine ⟨selected ++ [(group.positions, value)], ?_, ?_⟩
      · rw [← rankEq]
        exact .snoc previous group digit value (localCorrect.bounded digit value selectedDigit) selectedDigit
      · intro selectedGroup member index present
        rcases List.mem_append.mp member with old | last
        · exact agrees selectedGroup old index present
        · have same := List.mem_singleton.mp last
          subst selectedGroup
          exact selectedGroup_slots values group.positions value read (within group (by simp)) index present

/-- Read the selected value of the unique group that owns an index. -/
def assignment (fallback : Value) : List (List Nat × Value) → Nat → Value
  | [], _ => fallback
  | (positions, value) :: rest, index =>
      if index ∈ positions then value else assignment fallback rest index

/-- Disjoint group positions give an agreement function without an assumed assignment law. -/
theorem assignment_agrees (fallback : Value) (selected : List (List Nat × Value))
    (distinct : (selected.map Prod.fst).flatten.Nodup) :
    Agrees (assignment fallback selected) selected := by
  induction selected with
  | nil => simp [Agrees]
  | cons first rest ih =>
      have parts := List.nodup_append.mp distinct
      have tail := ih parts.2.1
      intro group member index present
      rcases List.mem_cons.mp member with rfl | member
      · simp [assignment, present]
      · have inTail : index ∈ (rest.map Prod.fst).flatten :=
          List.mem_flatten.mpr ⟨group.1, List.mem_map.mpr ⟨group, member, rfl⟩, present⟩
        have outside : index ∉ first.1 := fun inside => parts.2.2 index inside index inTail rfl
        simp only [assignment, outside, ↓reduceIte]
        exact tail group member index present

/-- Source Term.fromAssocs, with packing only at the already verified representation boundary. -/
def construct (symbol : Symbol) (arity : Nat) (selected : List (List Nat × Term Symbol)) : Option (Term Symbol) :=
  (ChildBuilder.fromAssocs symbol arity
    (slots (selected.map fun group => (group.1, TermRepresentation.pack group.2)))).map TermRepresentation.unpack

/-- The packed source builder restores all child positions in their original index order. -/
theorem construct_exact (symbol : Symbol) (value : Nat → Term Symbol)
    (selected : List (List Nat × Term Symbol)) (arity : Nat) (classes : List (List Nat))
    (groups : selected.map Prod.fst = childGroups arity classes) (agrees : Agrees value selected) :
    construct symbol arity selected = some (.node symbol ((List.range arity).map value)) := by
  have packedGroups : (selected.map (fun group => (group.1, TermRepresentation.pack group.2))).map Prod.fst =
      childGroups arity classes := by simpa only [List.map_map, Function.comp_def] using groups
  have packedAgrees : Agrees (fun index => TermRepresentation.pack (value index))
      (selected.map fun group => (group.1, TermRepresentation.pack group.2)) := by
    intro group member index present
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    subst group
    exact congrArg TermRepresentation.pack (agrees original originalMember index present)
  have built := fromAssocs_exact symbol (fun index => TermRepresentation.pack (value index)) _ arity classes packedGroups packedAgrees
  simp [construct, built, TermRepresentation.unpack_node, List.map_map, Function.comp_def, TermRepresentation.unpack_pack]

/-- Generated child values use the unique selected group at each valid index. -/
def childrenOf (symbol : Symbol) (arity : Nat) (selected : List (List Nat × Term Symbol)) : List (Term Symbol) :=
  (List.range arity).map (assignment (.node symbol []) selected)

/-- Every decoded group assignment fills the source child builder completely. -/
theorem construct_generated (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (selected : List (List Nat × Term Symbol)) (groups : selected.map Prod.fst = childGroups arity classes) :
    construct symbol arity selected = some (.node symbol (childrenOf symbol arity selected)) := by
  apply construct_exact symbol _ selected arity classes groups
  apply assignment_agrees
  rw [groups]
  exact childGroups_nodup arity classes

/-- Each generated child list agrees with every duplicated group slot. -/
theorem generated_agreement (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (selected : List (List Nat × Term Symbol)) (groups : selected.map Prod.fst = childGroups arity classes) :
    SlotAgreement (childrenOf symbol arity selected) selected := by
  have distinct : (selected.map Prod.fst).flatten.Nodup := by rw [groups]; exact childGroups_nodup arity classes
  have agrees := assignment_agrees (.node symbol []) selected distinct
  intro group member index present
  have grouped : group.1 ∈ childGroups arity classes := by
    rw [← groups]
    exact List.mem_map.mpr ⟨group, member, rfl⟩
  have within := List.mem_range.mp ((childGroups_positions arity classes).mem_iff.mp
    (List.mem_flatten.mpr ⟨group.1, grouped, present⟩))
  simp [childrenOf, within, agrees group member index present]

/-- The complete operational compact edge decoder, including actual child reconstruction. -/
def selectEdge (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol))) (rank : Nat) : Option (Term Symbol) :=
  ((plan groups).select rank).bind (construct symbol arity)

/-- The exact source edge inverse checks the constructor and arity before reading any group. -/
def rankEdge [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol))) :
    Term Symbol → Option Nat
  | .node found values => if found = symbol ∧ values.length = arity then rankFold values groups 0 else none

/-- The parsed group layout provides every local inverse reader with a nonempty in-range group. -/
theorem layout_local (arity : Nat) (classes : List (List Nat)) (valid : ValidClasses arity classes)
    (groups : List (Group Value)) (layout : groups.map Group.positions = childGroups arity classes) :
    (∀ group ∈ groups, group.positions ≠ []) ∧
      ∀ group ∈ groups, ∀ index ∈ group.positions, index < arity := by
  have membership : ∀ group ∈ groups, group.positions ∈ childGroups arity classes := by
    intro group member
    rw [← layout]
    exact List.mem_map.mpr ⟨group, member, rfl⟩
  constructor
  · intro group member
    exact childGroups_nonempty arity classes valid group.positions (membership group member)
  · intro group member index present
    exact List.mem_range.mp ((childGroups_positions arity classes).mem_iff.mp
      (List.mem_flatten.mpr ⟨group.positions, membership group member, present⟩))

/-- Every bounded rank decodes one complete edge term, including the nullary product. -/
theorem edge_total (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (rank : Nat) (within : rank < (plan groups).count) :
    ∃ term, selectEdge symbol arity groups rank = some term := by
  obtain ⟨selected, found⟩ := plan_total groups correct rank within
  have groupEq := (decoded_groups (select_decoded groups rank selected found)).trans layout
  exact ⟨.node symbol (childrenOf symbol arity selected), by
    simp [selectEdge, found, construct_generated symbol arity classes selected groupEq]⟩

/-- Every successful edge selection lies inside the exact folded cardinality. -/
theorem edge_bound (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol)))
    (rank : Nat) (term : Term Symbol) (found : selectEdge symbol arity groups rank = some term) :
    rank < (plan groups).count := by
  obtain ⟨selected, decoded, _⟩ := Option.bind_eq_some_iff.mp found
  exact decoded_bound (select_decoded groups rank selected decoded)

/-- The source rankEdge exactly reverses every successful compact edge selection. -/
theorem rank_select_edge [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (rank : Nat) (term : Term Symbol)
    (found : selectEdge symbol arity groups rank = some term) : rankEdge symbol arity groups term = some rank := by
  obtain ⟨selected, decoded, built⟩ := Option.bind_eq_some_iff.mp found
  have derivation := select_decoded groups rank selected decoded
  have groupEq := (decoded_groups derivation).trans layout
  have builtExact := construct_generated symbol arity classes selected groupEq
  have termEq := Option.some.inj (built.symm.trans builtExact)
  rw [termEq]
  have read := rankFold_decoded derivation correct (layout_local arity classes valid groups layout).1 _
    (generated_agreement symbol arity classes selected groupEq)
  simpa [rankEdge, childrenOf] using read


/-- Range-index reconstruction preserves every original child and its order. -/
theorem rebuild_values (fallback : Value) (values : List Value) :
    (List.range values.length).map (fun index => values[index]?.getD fallback) = values := by
  apply List.ext_getElem?
  intro index
  by_cases within : index < values.length
  · simp [within]
  · simp [within]

/-- The source builder reconstructs an existing child list from its agreed group values. -/
theorem construct_original (symbol : Symbol) (values : List (Term Symbol)) (classes : List (List Nat))
    (selected : List (List Nat × Term Symbol))
    (groups : selected.map Prod.fst = childGroups values.length classes) (agrees : SlotAgreement values selected) :
    construct symbol values.length selected = some (.node symbol values) := by
  have direct : Agrees (fun index => values[index]?.getD (.node symbol [])) selected := by
    intro group member index present
    simp [agrees group member index present]
  have built := construct_exact symbol (fun index => values[index]?.getD (.node symbol [])) selected values.length classes groups direct
  simpa only [rebuild_values] using built

/-- Every source inverse result decodes exactly its original complete edge term. -/
theorem select_rank_edge [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (term : Term Symbol) (rank : Nat)
    (found : rankEdge symbol arity groups term = some rank) : selectEdge symbol arity groups rank = some term := by
  cases term with
  | node foundSymbol values =>
      simp only [rankEdge] at found
      split at found
      next check =>
        obtain ⟨sameSymbol, sameSize⟩ := check
        subst foundSymbol
        have within := (layout_local arity classes valid groups layout).2
        obtain ⟨selected, decoded, agrees⟩ := rankFold_sound values groups correct
          (fun group member index present => by simpa only [sameSize] using within group member index present) rank found
        have groupEq : selected.map Prod.fst = childGroups values.length classes := by
          rw [decoded_groups decoded, layout, sameSize]
        have built := construct_original symbol values classes selected groupEq agrees
        simp [selectEdge, decoded_select decoded, ← sameSize, built]
      next => cases found

/-- The whole source compact edge decoder and inverse are exact in both directions. -/
theorem edge_inverse [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (term : Term Symbol) (rank : Nat) :
    rankEdge symbol arity groups term = some rank ↔ selectEdge symbol arity groups rank = some term :=
  ⟨select_rank_edge symbol arity classes valid groups layout correct term rank,
    rank_select_edge symbol arity classes valid groups layout correct rank term⟩

/-- Distinct compact edge ranks cannot decode the same complete term. -/
theorem edge_injective [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (first second : Nat) (term : Term Symbol)
    (a : selectEdge symbol arity groups first = some term) (b : selectEdge symbol arity groups second = some term) :
    first = second := by
  have ha := rank_select_edge symbol arity classes valid groups layout correct first term a
  have hb := rank_select_edge symbol arity classes valid groups layout correct second term b
  exact Option.some.inj (ha.symm.trans hb)

/-- Source inverse rejection means that no compact edge rank selects the requested term. -/
theorem edge_rejected [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (term : Term Symbol) :
    rankEdge symbol arity groups term = none ↔ ∀ rank, selectEdge symbol arity groups rank ≠ some term := by
  constructor
  · intro rejected rank selected
    have ranked := rank_select_edge symbol arity classes valid groups layout correct rank term selected
    rw [rejected] at ranked
    cases ranked
  · intro rejected
    cases found : rankEdge symbol arity groups term with
    | none => rfl
    | some rank => exact False.elim (rejected rank (select_rank_edge symbol arity classes valid groups layout correct term rank found))

/-- Exactly the ranks from zero to the product cardinality minus one decode. -/
theorem edge_rank_interval (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (rank : Nat) :
    (∃ term, selectEdge symbol arity groups rank = some term) ↔ rank < (plan groups).count :=
  ⟨fun ⟨term, found⟩ => edge_bound symbol arity groups rank term found,
    edge_total symbol arity classes groups layout correct rank⟩

/-- One empty child intersection makes the whole edge product empty. -/
theorem empty_group_count (groups : List (Group Value)) (group : Group Value)
    (member : group ∈ groups) (empty : group.index.count = 0) : (plan groups).count = 0 := by
  rw [plan_count]
  apply List.prod_eq_zero_iff_exists_zero_nat.mpr
  exact ⟨0, List.mem_map.mpr ⟨group, member, empty⟩, rfl⟩

/-- Empty group domains cannot produce an unchecked out-of-range edge member. -/
theorem empty_group_select (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol)))
    (group : Group (Term Symbol)) (member : group ∈ groups) (empty : group.index.count = 0) (rank : Nat) :
    selectEdge symbol arity groups rank = none := by
  cases found : selectEdge symbol arity groups rank with
  | none => rfl
  | some term =>
      have bound := edge_bound symbol arity groups rank term found
      rw [empty_group_count groups group member empty] at bound
      omega

/-- The nullary source fold selects exactly its one constructor. -/
theorem nullary_select (symbol : Symbol) (rank : Nat) :
    selectEdge symbol 0 [] rank = if rank = 0 then some (.node symbol []) else none := by
  by_cases zero : rank = 0 <;>
    simp [selectEdge, plan, unitPlan, zero, construct, slots, ChildBuilder.fromAssocs, TermRepresentation.unpack]

/-- Nullary inverse ranking checks the complete root and has no group digit. -/
theorem nullary_rank [DecidableEq Symbol] (symbol : Symbol) (term : Term Symbol) :
    rankEdge symbol 0 [] term = if term = .node symbol [] then some 0 else none := by
  cases term with
  | node found children => simp [rankEdge, rankFold]


/-- The source inverse succeeds exactly when every concrete group read and child inverse succeeds. -/
theorem rankFold_exists [DecidableEq Value] (values : List Value) (groups : List (Group Value)) (initial : Nat) :
    (∃ rank, rankFold values groups initial = some rank) ↔
      ∀ group ∈ groups, ∃ selected digit,
        selectedGroup values group.positions = some selected ∧ group.index.rank selected = some digit := by
  induction groups generalizing initial with
  | nil => simp [rankFold]
  | cons group rest ih =>
      constructor
      · rintro ⟨rank, found⟩
        obtain ⟨selected, read, tail⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨digit, digitFound, remainder⟩ := Option.bind_eq_some_iff.mp tail
        have later := (ih _).mp ⟨rank, remainder⟩
        intro next member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨selected, digit, read, digitFound⟩
        · exact later next member
      · intro all
        obtain ⟨selected, digit, read, digitFound⟩ := all group (by simp)
        obtain ⟨rank, later⟩ := (ih (pairRank group.index.count initial digit)).mpr
          (fun next member => all next (by simp [member]))
        exact ⟨rank, by simp [rankFold, read, digitFound, later]⟩

/-- A concrete child's indexed lookup, with an unused value outside its declared arity. -/
def childValue (fallback : Value) (values : List Value) (index : Nat) : Value := values[index]?.getD fallback

/-- Actual group reading and local intersection indexes enforce exactly the original child constraints. -/
theorem rankFold_language [DecidableEq Symbol] (symbol : Symbol) (domain : Nat → Term Symbol → Prop)
    (values : List (Term Symbol)) (classes : List (List Nat)) (valid : ValidClasses values.length classes)
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups values.length classes)
    (correct : ∀ group ∈ groups, Correct group.index)
    (domains : ∀ group ∈ groups, ∀ value,
      (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, domain index value) :
    (∃ rank, rankFold values groups 0 = some rank) ↔
      (∀ index, index < values.length → domain index (childValue (.node symbol []) values index)) ∧
        ∀ positions ∈ classes, EqualAt (childValue (.node symbol []) values) positions := by
  rw [rankFold_exists]
  rw [← groupSelections_exact domain (childValue (.node symbol []) values) values.length classes valid]
  have groupFacts := layout_local values.length classes valid groups layout
  constructor
  · intro ranked positions member
    have mapped : positions ∈ groups.map Group.positions := by simpa only [layout] using member
    obtain ⟨group, groupMember, same⟩ := List.mem_map.mp mapped
    subst positions
    obtain ⟨value, digit, read, ranked⟩ := ranked group groupMember
    have selected := (correct group groupMember).inverse digit value |>.mp ranked
    have accepted := (domains group groupMember value).mp ⟨digit, selected⟩
    have agrees := selectedGroup_slots values group.positions value read (groupFacts.2 group groupMember)
    exact ⟨value, fun index present => ⟨accepted index present, by simp [childValue, agrees index present]⟩⟩
  · intro selected group member
    have positionMember : group.positions ∈ childGroups values.length classes := by
      rw [← layout]
      exact List.mem_map.mpr ⟨group, member, rfl⟩
    obtain ⟨value, facts⟩ := selected group.positions positionMember
    obtain ⟨digit, chosen⟩ := (domains group member value).mpr (fun index present => (facts index present).1)
    refine ⟨value, digit, ?_, (correct group member).inverse digit value |>.mpr chosen⟩
    apply selectedGroup_exact values group.positions value (groupFacts.1 group member)
    intro index present
    have within := groupFacts.2 group member index present
    have same := (facts index present).2
    simpa [childValue, List.getElem?_eq_getElem within] using congrArg some same

/-- The exact language of one compact edge, before compact alternatives are concatenated. -/
def EdgeTerms (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (domain : Nat → Term Symbol → Prop) : Term Symbol → Prop
  | .node found values => found = symbol ∧ values.length = arity ∧
      (∀ index, index < values.length → domain index (childValue (.node symbol []) values index)) ∧
      ∀ positions ∈ classes, EqualAt (childValue (.node symbol []) values) positions

/-- Local child intersection semantics and the actual parser layout give the complete edge language. -/
theorem edge_language_exact [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (domain : Nat → Term Symbol → Prop)
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index)
    (domains : ∀ group ∈ groups, ∀ value,
      (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, domain index value)
    (term : Term Symbol) :
    (∃ rank, selectEdge symbol arity groups rank = some term) ↔ EdgeTerms symbol arity classes domain term := by
  have inverse : (∃ rank, selectEdge symbol arity groups rank = some term) ↔
      ∃ rank, rankEdge symbol arity groups term = some rank := by
    apply exists_congr
    intro rank
    exact (edge_inverse symbol arity classes valid groups layout correct term rank).symm
  rw [inverse]
  cases term with
  | node found values =>
      simp only [rankEdge, EdgeTerms]
      by_cases shape : found = symbol ∧ values.length = arity
      · obtain ⟨sameSymbol, sameSize⟩ := shape
        subst found
        simp only [sameSize, true_and, and_self, ↓reduceIte]
        simpa only [sameSize] using rankFold_language symbol domain values classes (sameSize ▸ valid) groups
          (by simpa only [sameSize] using layout) correct domains
      · simp only [shape, ↓reduceIte, reduceCtorEq, exists_false, false_iff]
        intro accepted
        exact shape ⟨accepted.1, accepted.2.1⟩

/-- A finite proof witness for the direct decoder's outputs; the operational decoder never constructs it. -/
def outputs (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol))) : List (Term Symbol) :=
  (List.range (plan groups).count).filterMap (selectEdge symbol arity groups)

/-- The proof witness contains exactly the direct decoder results. -/
theorem mem_outputs (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol))) (term : Term Symbol) :
    term ∈ outputs symbol arity groups ↔ ∃ rank, selectEdge symbol arity groups rank = some term := by
  simp only [outputs, List.mem_filterMap]
  constructor
  · rintro ⟨rank, _, selected⟩
    exact ⟨rank, selected⟩
  · rintro ⟨rank, selected⟩
    exact ⟨rank, List.mem_range.mpr (edge_bound symbol arity groups rank term selected), selected⟩

/-- Compact edge output uniqueness follows from the actual inverse, without duplicate removal. -/
theorem outputs_nodup [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) : (outputs symbol arity groups).Nodup := by
  apply List.pairwise_filterMap.mpr
  apply List.nodup_range.imp
  intro first second distinct a firstFound b secondFound same
  subst b
  exact distinct (edge_injective symbol arity classes valid groups layout correct first second a firstFound secondFound)

/-- The direct decoder supplies an exact distinct index for its complete constrained edge language. -/
def edgeIndex [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (domain : Nat → Term Symbol → Prop)
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index)
    (domains : ∀ group ∈ groups, ∀ value,
      (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, domain index value) :
    DistinctRank.Index (EdgeTerms symbol arity classes domain) where
  members := outputs symbol arity groups
  nodup := outputs_nodup symbol arity classes valid groups layout correct
  exact term := (mem_outputs symbol arity groups term).trans
    (edge_language_exact symbol arity classes valid domain groups layout correct domains term)


/-- The proof output list has exactly the operational product cardinality. -/
theorem outputs_count (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) :
    (outputs symbol arity groups).length = (plan groups).count := by
  have total : ∀ rank ∈ List.range (plan groups).count, (selectEdge symbol arity groups rank).isSome := by
    intro rank member
    obtain ⟨term, found⟩ := edge_total symbol arity classes groups layout correct rank (List.mem_range.mp member)
    simp [found]
  simpa only [outputs, List.length_range] using List.filterMap_length_eq_length.mpr total

/-- The compiled operational edge index packages the selector and its same-pass inverse. -/
def compiledEdge [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (groups : List (Group (Term Symbol))) : Index (Term Symbol) :=
  ⟨(plan groups).count, selectEdge symbol arity groups, rankEdge symbol arity groups⟩

/-- All three child-index induction obligations are derived for the complete parent edge. -/
theorem compiledEdge_correct [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (groups : List (Group (Term Symbol)))
    (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) : Correct (compiledEdge symbol arity groups) where
  bounded := edge_bound symbol arity groups
  total := edge_total symbol arity classes groups layout correct
  inverse rank term := edge_inverse symbol arity classes valid groups layout correct term rank

/-- A total partial selector can be materialized for proof without dropping or moving an entry. -/
theorem filterMap_total (fallback : Value) (select : α → Option Value) (items : List α)
    (total : ∀ item ∈ items, ∃ value, select item = some value) :
    items.filterMap select = items.map (fun item => (select item).getD fallback) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨value, selected⟩ := total first (by simp)
      simp [selected, ih (fun item member => total item (by simp [member]))]

/-- The exact source rank order agrees with the finite proof witness at every position. -/
theorem outputs_select (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index) (rank : Nat) :
    (outputs symbol arity groups)[rank]? = selectEdge symbol arity groups rank := by
  by_cases within : rank < (plan groups).count
  · have materialized := filterMap_total (.node symbol []) (selectEdge symbol arity groups)
      (List.range (plan groups).count)
      (fun index member => edge_total symbol arity classes groups layout correct index (List.mem_range.mp member))
    obtain ⟨term, selected⟩ := edge_total symbol arity classes groups layout correct rank within
    simp [outputs, materialized, within, selected]
  · have outside : (plan groups).count ≤ rank := by omega
    have listNone : (outputs symbol arity groups)[rank]? = none :=
      List.getElem?_eq_none (by rw [outputs_count symbol arity classes groups layout correct]; exact outside)
    rw [listNone]
    cases selected : selectEdge symbol arity groups rank with
    | none => rfl
    | some term => exact False.elim (within (edge_bound symbol arity groups rank term selected))

/-- Distinct language cardinality is the source product of child-intersection counts. -/
theorem edgeIndex_count [DecidableEq Symbol] (symbol : Symbol) (arity : Nat) (classes : List (List Nat))
    (valid : ValidClasses arity classes) (domain : Nat → Term Symbol → Prop)
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups arity classes)
    (correct : ∀ group ∈ groups, Correct group.index)
    (domains : ∀ group ∈ groups, ∀ value,
      (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, domain index value) :
    (edgeIndex symbol arity classes valid domain groups layout correct domains).count =
      (groups.map (fun group => group.index.count)).prod := by
  change (outputs symbol arity groups).length = _
  rw [outputs_count symbol arity classes groups layout correct, plan_count]

/-- Concrete finite leaf indexes for source arithmetic and reconstruction checks. -/
def leafIndex (count : Nat) : Index (Term Nat) where
  count := count
  select rank := if rank < count then some (.node rank []) else none
  rank term := match term with
    | .node symbol [] => if symbol < count then some symbol else none
    | _ => none

/-- The first equality group is the most significant digit and duplicates only its assigned slots. -/
theorem mixed_group_example :
    selectEdge 9 3 [⟨[0, 2], leafIndex 2⟩, ⟨[1], leafIndex 3⟩] 5 =
      some (.node 9 [.node 1 [], .node 2 [], .node 1 []]) ∧
    rankEdge 9 3 [⟨[0, 2], leafIndex 2⟩, ⟨[1], leafIndex 3⟩]
      (.node 9 [.node 1 [], .node 2 [], .node 1 []]) = some 5 := by cbv

/-- Unequal repeated children, wrong arity, and wrong constructors fail the actual inverse. -/
theorem rejection_examples :
    rankEdge 9 3 [⟨[0, 2], leafIndex 2⟩, ⟨[1], leafIndex 3⟩]
      (.node 9 [.node 0 [], .node 2 [], .node 1 []]) = none ∧
    rankEdge 9 3 [⟨[0, 2], leafIndex 2⟩, ⟨[1], leafIndex 3⟩] (.node 9 []) = none ∧
    rankEdge 9 3 [⟨[0, 2], leafIndex 2⟩, ⟨[1], leafIndex 3⟩]
      (.node 8 [.node 1 [], .node 2 [], .node 1 []]) = none := by cbv

/-- A zero-cardinality group has no selected term at rank zero. -/
theorem empty_group_example : selectEdge 9 1 [⟨[0], leafIndex 0⟩] 0 = none := by cbv


/-- Ordered child-domain evidence is exactly the source's indexed child lookup relation. -/
theorem all₂_positions (relation : State → Value → Prop) (states : List State) (values : List Value) (fallback : Value) :
    All₂ relation states values ↔ states.length = values.length ∧
      ∀ index, index < values.length → ∃ state,
        states[index]? = some state ∧ relation state (childValue fallback values index) := by
  induction states generalizing values with
  | nil =>
      cases values with
      | nil => exact ⟨fun _ => ⟨rfl, by simp⟩, fun _ => .nil⟩
      | cons value rest =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; simp at impossible
  | cons state states ih =>
      cases values with
      | nil =>
          constructor
          · intro impossible; cases impossible
          · intro impossible; simp at impossible
      | cons value values =>
          constructor
          · intro related
            cases related with
            | cons head tail =>
                obtain ⟨lengthEq, remaining⟩ := (ih values).mp tail
                refine ⟨by simp [lengthEq], ?_⟩
                intro index bound
                cases index with
                | zero => exact ⟨state, rfl, head⟩
                | succ index =>
                    obtain ⟨next, found, accepted⟩ := remaining index (by simpa using bound)
                    exact ⟨next, by simpa using found, accepted⟩
          · rintro ⟨lengthEq, children⟩
            obtain ⟨head, found, accepted⟩ := children 0 (by simp)
            have same : state = head := Option.some.inj found
            subst head
            apply All₂.cons accepted
            apply (ih values).mpr
            refine ⟨by simpa using lengthEq, ?_⟩
            intro index within
            obtain ⟨next, found, accepted⟩ := children (index + 1) (by simp; omega)
            exact ⟨next, by simpa using found, accepted⟩

/-- The local domain of a child position is the domain of the exact stored child state. -/
def positionDomain (domain : State → Term Symbol → Prop) (children : List State) (index : Nat) (term : Term Symbol) : Prop :=
  ∃ state, children[index]? = some state ∧ domain state term

/-- The parser's direct equality guard and stored child list connect the compact language to an actual edge. -/
theorem edgeTerms_source (domain : State → Term Symbol → Prop) (edge : Edge State Symbol)
    (classes : List (List Nat))
    (guard : ∀ values : List (Term Symbol), values.length = edge.children.length →
      (edge.guard (.node edge.label values) = true ↔
        ∀ positions ∈ classes, EqualAt (childValue (.node edge.label []) values) positions))
    (term : Term Symbol) :
    EdgeTerms edge.label edge.children.length classes (positionDomain domain edge.children) term ↔
      AutomatonAmbiguity.EdgeLanguage domain edge term := by
  cases term with
  | node symbol values =>
      constructor
      · rintro ⟨sameSymbol, sameSize, children, equalities⟩
        subst symbol
        refine ⟨values, rfl, ?_, (guard values sameSize).mpr equalities⟩
        exact (all₂_positions domain edge.children values (.node edge.label [])).mpr ⟨sameSize.symm, children⟩
      · rintro ⟨original, same, related, accepted⟩
        obtain ⟨sameSymbol, sameChildren⟩ := Term.node.inj same
        subst symbol
        subst original
        obtain ⟨sameSize, children⟩ := (all₂_positions domain edge.children values (.node edge.label [])).mp related
        exact ⟨rfl, sameSize.symm, children, (guard values sameSize.symm).mp accepted⟩

/-- The actual edge decoder supplies the exact output-language premise of compactIndex. -/
theorem source_outputs_exact [DecidableEq Symbol] (domain : State → Term Symbol → Prop) (edge : Edge State Symbol)
    (classes : List (List Nat)) (valid : ValidClasses edge.children.length classes)
    (groups : List (Group (Term Symbol))) (layout : groups.map Group.positions = childGroups edge.children.length classes)
    (correct : ∀ group ∈ groups, Correct group.index)
    (domains : ∀ group ∈ groups, ∀ value,
      (∃ rank, group.index.select rank = some value) ↔ ∀ index ∈ group.positions, positionDomain domain edge.children index value)
    (guard : ∀ values : List (Term Symbol), values.length = edge.children.length →
      (edge.guard (.node edge.label values) = true ↔
        ∀ positions ∈ classes, EqualAt (childValue (.node edge.label []) values) positions))
    (term : Term Symbol) :
    term ∈ outputs edge.label edge.children.length groups ↔ AutomatonAmbiguity.EdgeLanguage domain edge term :=
  (mem_outputs edge.label edge.children.length groups term).trans
    ((edge_language_exact edge.label edge.children.length classes valid (positionDomain domain edge.children)
      groups layout correct domains term).trans (edgeTerms_source domain edge classes guard term))


end MicroCFTA.CompactEdgeRanks
