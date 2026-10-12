import MicroCFTA.RecursiveCallbackAPI
import MicroCFTA.RecursiveCallbackDistinct

/-!
# Arbitrary ordered recursive term alternatives

This module models `choiceTerms` with one list of count, selector, and
callback fields. Whole requests select the private branch. Spine requests
use the whole request. Labelled requests visit every branch. The adapter
retains all branch numbers, including numbers greater than one.

The contracts apply to each child field. They do not assume an inverse law
for the resulting choice. This is a local source adapter. It does not extend
the binary recursive body syntax to arbitrary heterogeneous recursive knots.
-/
namespace MicroCFTA.RecursiveNaryChoice
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct

/-- Keep the source's private branch label on the complete child term. -/
def wrap (branch : Nat) (term : EngineTerm Symbol) : EngineTerm Symbol :=
  .node (.choice branch) [term]

/-- Every offset and selector reads the same list of child fields. -/
def childCounts (children : List (Finite Symbol)) : List (Nat → Nat) := children.map Finite.counts

/-- Each size class contains the sum of its ordered child counts. -/
def count (children : List (Finite Symbol)) (size : Nat) : Nat :=
  (children.map fun child => child.counts size).sum

/-- Use the source prefix decoder and the selected child's term selector. -/
def select (children : List (Finite Symbol)) : Position → Option (EngineTerm Symbol) :=
  RecursiveCheckedRanks.selectChoice (childCounts children) (children.map Finite.select)

/-- Offset one child row and preserve its checked flag. -/
def offset (children : List (Finite Symbol)) (branch : Nat) : Checked → Checked :=
  RecursiveCheckedRanks.choiceRow (childCounts children) branch

/-- Only a present branch runs its callback. -/
def branchRows (children : List (Finite Symbol)) (branch : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) : List Checked :=
  match children[branch]? with
  | none => []
  | some child => (child.positions view wanted).map (offset children branch)

/-- Whole requests require one complete private choice node. -/
def wholeRows (children : List (Finite Symbol)) : List (EngineTerm Symbol) → List Checked
  | [.node (.choice branch) [term]] => branchRows children branch .whole [term]
  | _ => []

/-- Labelled requests concatenate every branch before the source sort. -/
def labelledRows (children : List (Finite Symbol)) (wanted : List (EngineTerm Symbol)) : List Checked :=
  (List.range children.length).flatMap fun branch => branchRows children branch .labelled wanted

/-- The spine path retains the source's outer sort and its whole-request sort. -/
def positions (children : List (Finite Symbol)) (view : View)
    (wanted : List (EngineTerm Symbol)) : List Checked :=
  match view with
  | .whole => sorted (wholeRows children wanted)
  | .spine => sorted (sorted (wholeRows children wanted))
  | .labelled => sorted (labelledRows children wanted)

/-- The assembled field can itself be used as a child of another adapter. -/
def field (children : List (Finite Symbol)) : Finite Symbol :=
  ⟨count children, select children, positions children⟩

/-- A successful prefix split identifies its exact count and inverse offset. -/
theorem split_sound (counts : List Nat) (rank branch innerRank : Nat)
    (found : choiceSplit counts rank = some (branch, innerRank)) :
    ∃ amount, counts[branch]? = some amount ∧ innerRank < amount ∧
      choicePosition counts branch innerRank = rank := by
  induction counts generalizing rank branch innerRank with
  | nil => simp [choiceSplit] at found
  | cons head rest ih =>
      simp only [choiceSplit] at found
      split at found
      · rename_i within
        have same := Option.some.inj found
        cases same
        exact ⟨head, by simp, within, by simp [choicePosition]⟩
      · rename_i outside
        obtain ⟨pair, selected, same⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨amount, present, within, inverse⟩ := ih _ _ _ selected
        cases same
        refine ⟨amount, by simpa using present, within, ?_⟩
        simp only [choicePosition, List.take_succ_cons, List.sum_cons]
        simp only [choicePosition] at inverse
        omega

/-- Prefix decoding succeeds exactly below the sum of all branch counts. -/
theorem split_total (counts : List Nat) (rank : Nat) :
    (∃ pair, choiceSplit counts rank = some pair) ↔ rank < counts.sum := by
  induction counts generalizing rank with
  | nil => simp [choiceSplit]
  | cons head rest ih =>
      by_cases within : rank < head
      · simp [choiceSplit, within]; omega
      · simp only [choiceSplit, within, ↓reduceIte, List.sum_cons]
        constructor
        · rintro ⟨pair, found⟩
          obtain ⟨original, selected, _⟩ := Option.map_eq_some_iff.mp found
          have := (ih (rank - head)).mp ⟨original, selected⟩
          omega
        · intro bound
          obtain ⟨pair, found⟩ := (ih (rank - head)).mpr (by omega)
          exact ⟨(pair.1 + 1, pair.2), by simp [found]⟩

/-- A valid branch offset stays within the complete class count. -/
theorem offset_bound (children : List (Finite Symbol)) (branch : Nat) (child : Finite Symbol)
    (present : children[branch]? = some child) (row : Checked)
    (within : row.1.rank < child.counts row.1.size) :
    (offset children branch row).1.rank < count children (offset children branch row).1.size := by
  apply (split_total _ _).mp
  refine ⟨(branch, row.1.rank), ?_⟩
  simp only [offset, RecursiveCheckedRanks.choiceRow, childCounts, List.map_map, Function.comp_def]
  exact choiceSplit_choicePosition _ branch row.1.rank (child.counts row.1.size)
    (by simp [List.getElem?_map, present]) within

/-- Offsets identify both the branch and child position on valid class intervals. -/
theorem offset_injective (children : List (Finite Symbol)) (a b : Nat)
    (first second : Finite Symbol) (firstPresent : children[a]? = some first)
    (secondPresent : children[b]? = some second) (p q : Checked)
    (pv : p.1.rank < first.counts p.1.size) (qv : q.1.rank < second.counts q.1.size)
    (same : (offset children a p).1 = (offset children b q).1) : a = b ∧ p.1 = q.1 := by
  have sizes : p.1.size = q.1.size := by
    simpa only [offset, RecursiveCheckedRanks.choiceRow] using congrArg Position.size same
  have ranks := congrArg Position.rank same
  have firstSplit := choiceSplit_choicePosition
    (children.map fun child => child.counts p.1.size) a p.1.rank (first.counts p.1.size)
    (by simp [List.getElem?_map, firstPresent]) pv
  have secondSplit := choiceSplit_choicePosition
    (children.map fun child => child.counts q.1.size) b q.1.rank (second.counts q.1.size)
    (by simp [List.getElem?_map, secondPresent]) qv
  simp only [offset, RecursiveCheckedRanks.choiceRow, childCounts, List.map_map,
    Function.comp_def] at ranks
  rw [sizes] at ranks firstSplit
  rw [ranks, secondSplit] at firstSplit
  have eqs := Prod.mk.inj (Option.some.inj firstSplit)
  exact ⟨eqs.1.symm, by rcases p with ⟨⟨ps, pr⟩, pf⟩; rcases q with ⟨⟨qs, qr⟩, qf⟩; simp_all⟩

/-- A valid selected child replays at its exact ordered choice position. -/
theorem select_offset (children : List (Finite Symbol)) (branch : Nat) (child : Finite Symbol)
    (present : children[branch]? = some child) (position : Position) (term : EngineTerm Symbol)
    (within : position.rank < child.counts position.size) (selected : child.select position = some term) :
    select children (offset children branch (position, true)).1 = some (wrap branch term) := by
  exact RecursiveCheckedRanks.choice_checked _ _ branch child.counts child.select
    (by simp [childCounts, List.getElem?_map, present])
    (by simp [List.getElem?_map, present]) position term within selected

/-- Every decoded choice comes from one child at its exact source offset. -/
theorem select_origin (children : List (Finite Symbol)) (position : Position) (term : EngineTerm Symbol)
    (selected : select children position = some term) :
    ∃ branch child innerPos childTerm, children[branch]? = some child ∧
      child.select innerPos = some childTerm ∧ innerPos.rank < child.counts innerPos.size ∧
      (offset children branch (innerPos, true)).1 = position ∧ term = wrap branch childTerm := by
  simp only [select, RecursiveCheckedRanks.selectChoice, bind, Option.bind_eq_some_iff] at selected
  obtain ⟨pair, split, selector, selectorFound, childTerm, childFound, same⟩ := selected
  obtain ⟨child, present, selectorEq⟩ := Option.map_eq_some_iff.mp (by
    simpa only [List.getElem?_map] using selectorFound)
  subst selector
  obtain ⟨amount, countFound, within, inverse⟩ := split_sound _ _ _ _ split
  have amountEq : child.counts position.size = amount := by
    simpa [childCounts, List.map_map, List.getElem?_map, present] using countFound
  refine ⟨pair.1, child, ⟨position.size, pair.2⟩, childTerm, present, childFound,
    by simpa [← amountEq] using within, ?_, ?_⟩
  · cases position
    simp_all [offset, RecursiveCheckedRanks.choiceRow]
  · exact (Option.some.inj same).symm

/-- Child count/selector contracts imply the complete choice count/selector contract. -/
theorem field_indexed (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child) : FiniteIndex (field children) := by
  intro position
  change (∃ term, select children position = some term) ↔ position.rank < count children position.size
  constructor
  · rintro ⟨term, selected⟩
    obtain ⟨branch, child, innerPos, childTerm, present, _, within, same, _⟩ := select_origin children position term selected
    have := offset_bound children branch child present (innerPos, true) within
    simpa only [same] using this
  · intro within
    obtain ⟨pair, split⟩ := (split_total (children.map fun child => child.counts position.size) position.rank).mpr (by simpa only [count] using within)
    obtain ⟨amount, countFound, bound, inverse⟩ := split_sound _ _ _ _ split
    obtain ⟨child, present, amountEq⟩ := Option.map_eq_some_iff.mp (by
      simpa only [List.getElem?_map] using countFound)
    obtain ⟨term, selected⟩ := (indexed child (List.mem_of_getElem? present) ⟨position.size, pair.2⟩).mpr
      (by simpa [amountEq] using bound)
    have replay := select_offset children pair.1 child present ⟨position.size, pair.2⟩ term
      (by simpa [amountEq] using bound) selected
    have same : (offset children pair.1 (⟨position.size, pair.2⟩, true)).1 = position := by
      cases position
      simp_all [offset, RecursiveCheckedRanks.choiceRow, childCounts, List.map_map, Function.comp_def]
    exact ⟨wrap pair.1 term, by simpa only [same] using replay⟩

/-- The forward choice index maps each class and concatenates the branches in order. -/
def groups (children : List (Finite Symbol)) (size : Nat) : List (List (EngineTerm Symbol)) :=
  children.mapIdx fun branch child => (finiteClass child size).map (wrap branch)

/-- The independent ordered table keeps complete private choice terms. -/
def classTerms (children : List (Finite Symbol)) (size : Nat) : List (EngineTerm Symbol) :=
  (groups children size).flatten

/-- Every mapped branch has the same term count as its child field. -/
theorem group_counts (children : List (Finite Symbol)) (size : Nat) :
    (groups children size).map List.length = children.map (fun child => child.counts size) := by
  apply List.ext_getElem?
  intro branch
  simp [groups, List.getElem?_map, List.getElem?_mapIdx, Option.map_map, Function.comp_def, finite_length]

/-- The independently constructed term table has the complete choice class count. -/
theorem class_length (children : List (Finite Symbol)) (size : Nat) :
    (classTerms children size).length = count children size := by
  simp only [classTerms, List.length_flatten, group_counts, count]

/-- The source offset replays through concatenated class tables in branch order. -/
theorem class_replay (children : List (Finite Symbol)) (branch : Nat) (child : Finite Symbol)
    (present : children[branch]? = some child) (indexed : FiniteIndex child)
    (p : Position) (term : EngineTerm Symbol) (selected : child.select p = some term) :
    (classTerms children p.size)[(offset children branch (p, true)).1.rank]? = some (wrap branch term) := by
  have branchValid := (List.getElem?_eq_some_iff.mp present).1
  have childEq := (List.getElem?_eq_some_iff.mp present).2
  have groupValid : branch < (groups children p.size).length := by simpa [groups] using branchValid
  have groupEq : (groups children p.size)[branch] = (finiteClass child p.size).map (wrap branch) := by
    simp [groups, childEq]
  have selectedTable := (finite_lookup child indexed p term).mpr selected
  have within : p.rank < ((groups children p.size)[branch]).length := by
    rw [groupEq, List.length_map]
    exact (List.getElem?_eq_some_iff.mp selectedTable).1
  have replay := get_choicePosition (groups children p.size) branch p.rank groupValid within
  rw [group_counts, groupEq, List.getElem?_map, selectedTable] at replay
  simpa only [classTerms, offset, RecursiveCheckedRanks.choiceRow, childCounts, List.map_map,
    Function.comp_def, Option.map_some] using replay

/-- The direct prefix decoder agrees at every rank with the independent forward class order. -/
theorem select_table (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child) (position : Position) :
    select children position = (classTerms children position.size)[position.rank]? := by
  cases selected : select children position with
  | some term =>
      obtain ⟨branch, child, p, childTerm, present, childSelected, _, same, rfl⟩ :=
        select_origin children position term selected
      have replay := class_replay children branch child present
        (indexed child (List.mem_of_getElem? present)) p childTerm childSelected
      have sizeEq : p.size = position.size := by
        simpa only [offset, RecursiveCheckedRanks.choiceRow] using congrArg Position.size same
      have rankEq := congrArg Position.rank same
      rw [sizeEq, rankEq] at replay
      exact replay.symm
  | none =>
      have outside : ¬position.rank < count children position.size := by
        intro within
        obtain ⟨term, found⟩ := (field_indexed children indexed position).mpr within
        change select children position = some term at found
        rw [selected] at found
        cases found
      symm
      exact List.getElem?_eq_none (by simpa only [class_length] using Nat.le_of_not_gt outside)

/-- Whole and spine views retain the complete private choice node. -/
theorem project_wrap (branch : Nat) (term : EngineTerm Symbol) :
    project .whole (wrap branch term) = [wrap branch term] ∧
    project .spine (wrap branch term) = [wrap branch term] ∧
    project .labelled (wrap branch term) = project .labelled term := by
  simp [wrap, project, labelled, spine, SupportTerms.applicationLeftChildren,
    SupportTerms.applicationTermChildren]

/-- Branch adaptation preserves the complete original row, including false flags. -/
theorem branch_member (children : List (Finite Symbol)) (branch : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked) :
    row ∈ branchRows children branch view wanted ↔
      ∃ child original, children[branch]? = some child ∧
        original ∈ child.positions view wanted ∧ offset children branch original = row := by
  cases found : children[branch]? <;> simp [branchRows, found, List.mem_map]

/-- True child certificates replay the exact offset and requested child view. -/
theorem branch_certified (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, FiniteExact child)
    (branch : Nat) (view : View) (wanted : List (EngineTerm Symbol)) (position : Position)
    (member : (position, true) ∈ branchRows children branch view wanted) :
    ∃ term, select children position = some (wrap branch term) ∧ project view term = wanted := by
  obtain ⟨child, ⟨p, flag⟩, present, member, same⟩ := (branch_member children branch view wanted _).mp member
  have flagEq : flag = true := congrArg Prod.snd same
  subst flag
  obtain ⟨term, selected, projected⟩ := (exactChildren child (List.mem_of_getElem? present) view wanted p).mp member
  have within := (indexed child (List.mem_of_getElem? present) p).mp ⟨term, selected⟩
  have replay := select_offset children branch child present p term within selected
  have positionsEq := congrArg Prod.fst same
  exact ⟨term, by simpa only [positionsEq] using replay, projected⟩

/-- Each successful child selector supplies a true branch row in every view. -/
theorem branch_complete (children : List (Finite Symbol))
    (exactChildren : ∀ child ∈ children, FiniteExact child)
    (branch : Nat) (child : Finite Symbol) (present : children[branch]? = some child)
    (p : Position) (term : EngineTerm Symbol) (selected : child.select p = some term) (view : View) :
    ((offset children branch (p, true)).1, true) ∈ branchRows children branch view (project view term) := by
  apply (branch_member children branch view (project view term) _).mpr
  exact ⟨child, (p, true), present,
    (exactChildren child (List.mem_of_getElem? present) view (project view term) p).mpr ⟨term, selected, rfl⟩,
    rfl⟩

/-- A whole request can return rows only from its stated private branch. -/
theorem whole_origin (children : List (Finite Symbol)) (wanted : List (EngineTerm Symbol))
    (row : Checked) (member : row ∈ wholeRows children wanted) :
    ∃ branch term, wanted = [wrap branch term] ∧ row ∈ branchRows children branch .whole [term] := by
  unfold wholeRows at member
  split at member
  · exact ⟨_, _, rfl, member⟩
  · simp at member

/-- The arbitrary-arity choice has all and only certified decoder preimages. -/
theorem field_exact (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, FiniteExact child) : FiniteExact (field children) := by
  intro view wanted position
  change (position, true) ∈ positions children view wanted ↔
    ∃ term, select children position = some term ∧ project view term = wanted
  constructor
  · intro member
    cases view with
    | whole | spine =>
        simp only [positions, mem_sorted] at member
        obtain ⟨branch, term, rfl, member⟩ := whole_origin children wanted _ member
        obtain ⟨child, selected, projected⟩ := branch_certified children indexed exactChildren branch .whole [term] position member
        have same : child = term := by simpa [project] using projected
        subst child
        exact ⟨wrap branch term, selected, by simp [project_wrap]⟩
    | labelled =>
        obtain ⟨branch, _, member⟩ := List.mem_flatMap.mp ((mem_sorted _ _).mp member)
        obtain ⟨term, selected, projected⟩ := branch_certified children indexed exactChildren branch .labelled wanted position member
        exact ⟨wrap branch term, selected, (project_wrap branch term).2.2.trans projected⟩
  · rintro ⟨term, selected, rfl⟩
    obtain ⟨branch, child, p, childTerm, present, childSelected, _, same, rfl⟩ := select_origin children position term selected
    have complete := branch_complete children exactChildren branch child present p childTerm childSelected
    cases view with
    | whole | spine =>
        simp only [positions, mem_sorted, (project_wrap branch childTerm).1,
          (project_wrap branch childTerm).2.1]
        simpa only [wrap, wholeRows, project, same] using complete .whole
    | labelled =>
        rw [positions, mem_sorted, (project_wrap branch childTerm).2.2]
        exact List.mem_flatMap.mpr ⟨branch,
          List.mem_range.mpr (List.getElem?_eq_some_iff.mp present).1,
          by simpa only [same] using complete .labelled⟩

/-- Every child candidate stays within its own class, regardless of its flag. -/
def Bounded (source : Finite Symbol) : Prop :=
  ∀ view wanted row, row ∈ source.positions view wanted → row.1.rank < source.counts row.1.size

/-- Every child callback retains distinct class positions. -/
def Unique (source : Finite Symbol) : Prop :=
  ∀ view wanted, Distinct (source.positions view wanted)

/-- Every row of one branch stays inside the complete choice class. -/
theorem branch_bound (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child)
    (branch : Nat) (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked)
    (member : row ∈ branchRows children branch view wanted) :
    row.1.rank < count children row.1.size := by
  obtain ⟨child, original, present, childMember, same⟩ := (branch_member children branch view wanted row).mp member
  rw [← same]
  exact offset_bound children branch child present original
    (bounded child (List.mem_of_getElem? present) view wanted original childMember)

/-- The complete callback returns only valid positions, including false certificates. -/
theorem field_bounded (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) : Bounded (field children) := by
  intro view wanted row member
  change row.1.rank < count children row.1.size
  change row ∈ positions children view wanted at member
  cases view with
  | whole | spine =>
      simp only [positions, mem_sorted] at member
      obtain ⟨branch, term, _, member⟩ := whole_origin children wanted row member
      exact branch_bound children bounded branch .whole [term] row member
  | labelled =>
      obtain ⟨branch, _, member⟩ := List.mem_flatMap.mp ((mem_sorted _ _).mp member)
      exact branch_bound children bounded branch .labelled wanted row member

/-- Source sorting gives the exact size, class-rank, and checked-flag order. -/
theorem positions_ordered (children : List (Finite Symbol)) (view : View)
    (wanted : List (EngineTerm Symbol)) :
    (positions children view wanted).Pairwise (fun a b => before a b) := by
  cases view <;> exact sorted_ordered _

/-- A branch cannot identify two distinct valid child positions. -/
theorem branch_distinct (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (unique : ∀ child ∈ children, Unique child)
    (branch : Nat) (view : View) (wanted : List (EngineTerm Symbol)) :
    Distinct (branchRows children branch view wanted) := by
  cases present : children[branch]? with
  | none => simp [branchRows, present, Distinct]
  | some child =>
      rw [branchRows, present, Distinct, List.pairwise_map]
      apply (unique child (List.mem_of_getElem? present) view wanted).imp_of_mem
      intro a b am bm different same
      exact different (offset_injective children branch branch child child present present a b
        (bounded child (List.mem_of_getElem? present) view wanted a am)
        (bounded child (List.mem_of_getElem? present) view wanted b bm) same).2

/-- Distinct branches cannot share a valid class position. -/
theorem branches_disjoint (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (a b : Nat) (different : a ≠ b)
    (view : View) (wanted : List (EngineTerm Symbol)) (p q : Checked)
    (pm : p ∈ branchRows children a view wanted) (qm : q ∈ branchRows children b view wanted) :
    p.1 ≠ q.1 := by
  obtain ⟨first, x, fp, xm, firstEq⟩ := (branch_member children a view wanted p).mp pm
  obtain ⟨second, y, sp, ym, secondEq⟩ := (branch_member children b view wanted q).mp qm
  intro same
  exact different (offset_injective children a b first second fp sp x y
    (bounded first (List.mem_of_getElem? fp) view wanted x xm)
    (bounded second (List.mem_of_getElem? sp) view wanted y ym)
    (by simpa only [firstEq, secondEq] using same)).1

/-- Concatenating all alternatives retains distinct positions before sorting. -/
theorem labelled_distinct (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (unique : ∀ child ∈ children, Unique child)
    (wanted : List (EngineTerm Symbol)) : Distinct (labelledRows children wanted) := by
  rw [Distinct, labelledRows, List.pairwise_flatMap]
  constructor
  · intro branch _
    exact branch_distinct children bounded unique branch .labelled wanted
  · exact (List.nodup_range (n := children.length)).imp
      (fun different p pm q qm => branches_disjoint children bounded _ _ different .labelled wanted p q pm qm)

/-- Whole requests retain the selected branch's position distinctness. -/
theorem whole_distinct (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (unique : ∀ child ∈ children, Unique child)
    (wanted : List (EngineTerm Symbol)) : Distinct (wholeRows children wanted) := by
  unfold wholeRows
  split
  · exact branch_distinct children bounded unique _ .whole _
  · exact .nil

/-- All source candidate positions are distinct, including unchecked candidates. -/
theorem field_unique (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (unique : ∀ child ∈ children, Unique child) :
    Unique (field children) := by
  intro view wanted
  change Distinct (positions children view wanted)
  cases view with
  | whole => exact sorted_distinct _ (whole_distinct children bounded unique wanted)
  | spine => exact sorted_distinct _ (sorted_distinct _ (whole_distinct children bounded unique wanted))
  | labelled => exact sorted_distinct _ (labelled_distinct children bounded unique wanted)

/-- True certificates bypass replay; false certificates check the selected view. -/
def keep [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked) : Bool :=
  row.2 || decide ((select children row.1).map (project view) = some wanted)

/-- The public inverse query retains callback order while it filters candidates. -/
def query [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (view : View) (wanted : List (EngineTerm Symbol)) : List Position :=
  ((positions children view wanted).filter (keep children view wanted)).map Prod.fst

/-- The public checked-flag filter returns every matching decoder position exactly. -/
theorem query_exact [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, FiniteExact child)
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    position ∈ query children view wanted ↔
      ∃ term, select children position = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨row, filtered, same⟩ := List.mem_map.mp member
    obtain ⟨present, kept⟩ := List.mem_filter.mp filtered
    rcases Bool.or_eq_true_iff.mp kept with checked | replayed
    · have rowEq : row = (position, true) := Prod.ext same checked
      exact (field_exact children indexed exactChildren view wanted position).mp (rowEq ▸ present)
    · have replay : (select children position).map (project view) = some wanted := by
        rw [← same]
        exact of_decide_eq_true replayed
      exact Option.map_eq_some_iff.mp replay
  · intro found
    have present := (field_exact children indexed exactChildren view wanted position).mpr found
    exact List.mem_map.mpr ⟨(position, true), List.mem_filter.mpr ⟨present, by simp [keep]⟩, rfl⟩

/-- Whole queries invert the complete private choice term. -/
theorem whole_query [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, FiniteExact child) (term : EngineTerm Symbol) (position : Position) :
    position ∈ query children .whole [term] ↔ select children position = some term := by
  rw [query_exact children indexed exactChildren]
  simp [project]

/-- The public inverse cannot repeat a class position. -/
theorem query_nodup [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (bounded : ∀ child ∈ children, Bounded child) (unique : ∀ child ∈ children, Unique child)
    (view : View) (wanted : List (EngineTerm Symbol)) : (query children view wanted).Nodup := by
  apply (distinct_iff _).mp
  exact (field_unique children bounded unique view wanted).filter _

/-- Public positions retain ascending size and class rank after candidate filtering. -/
theorem query_ordered [DecidableEq (EngineTerm Symbol)] (children : List (Finite Symbol))
    (view : View) (wanted : List (EngineTerm Symbol)) :
    (query children view wanted).Pairwise
      (fun p q => p.size < q.size ∨ (p.size = q.size ∧ p.rank ≤ q.rank)) := by
  rw [query, List.pairwise_map]
  apply ((positions_ordered children view wanted).sublist List.filter_sublist).imp
  intro first second ordered
  simp only [before, decide_eq_true_eq] at ordered
  omega

open RecursiveCallbackAlignment

/-- Use a compiled recursive body's actual value counts, term decoder, and tied callback. -/
def recursiveField [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root) : Finite Symbol :=
  ⟨RecursiveCallbackAPI.selfCounts body, RecursiveCallbackAPI.decode body,
    tied (RecursiveCallbackAPI.selfCounts body) (compile callbacks body)⟩

/-- The independently compiled value and term fields supply the child count contract. -/
theorem recursive_indexed [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root) : FiniteIndex (recursiveField callbacks body) := by
  intro position
  change (∃ term, RecursiveCallbackAPI.decode body position = some term) ↔
    position.rank < RecursiveCallbackAPI.selfCounts body position.size
  simp only [RecursiveCallbackAPI.decode_table, ← RecursiveCallbackAPI.root_counts]
  constructor
  · rintro ⟨term, found⟩
    exact (List.getElem?_eq_some_iff.mp found).1
  · intro within
    exact ⟨_, List.getElem?_eq_getElem within⟩

/-- Only local finite-leaf inverse laws are required to certify a recursive child. -/
theorem recursive_exact [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body)) : FiniteExact (recursiveField callbacks body) :=
  RecursiveCallbackAPI.certified_query callbacks body accepted leaves

/-- The source count equation supplies all candidate bounds for a recursive child. -/
theorem recursive_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesBounded (compile callbacks body)) : Bounded (recursiveField callbacks body) := by
  intro view wanted row member
  exact positions_bound (RecursiveCallbackAPI.selfCounts body) (compile callbacks body)
    (RecursiveCallbackAPI.count_knot callbacks body accepted) leaves .occurrence trivial view wanted row member

/-- Local finite-leaf bounds and distinctness certify the complete recursive child. -/
theorem recursive_unique [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (bounded : LeavesBounded (compile callbacks body))
    (distinct : LeavesDistinct (compile callbacks body)) : Unique (recursiveField callbacks body) := by
  intro view wanted
  exact positions_distinct (RecursiveCallbackAPI.selfCounts body) (compile callbacks body)
    (RecursiveCallbackAPI.count_knot callbacks body accepted) bounded distinct .occurrence trivial trivial view wanted

/-- Arbitrarily many compiled recursive children satisfy the n-way inverse contract. -/
theorem recursive_choices_exact [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (bodies : List (RecursiveTermAlignment.Recipe Root Symbol Root))
    (accepted : ∀ body ∈ bodies, RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : ∀ body ∈ bodies, LeavesExact (compile callbacks body)) :
    FiniteExact (field (bodies.map (recursiveField callbacks))) := by
  apply field_exact
  · intro child member
    obtain ⟨body, _, rfl⟩ := List.mem_map.mp member
    exact recursive_indexed callbacks body
  · intro child member
    obtain ⟨body, present, rfl⟩ := List.mem_map.mp member
    exact recursive_exact callbacks body (accepted body present) (leaves body present)

/-- Arbitrarily many compiled recursive children retain all candidate bounds. -/
theorem recursive_choices_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (bodies : List (RecursiveTermAlignment.Recipe Root Symbol Root))
    (accepted : ∀ body ∈ bodies, RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : ∀ body ∈ bodies, LeavesBounded (compile callbacks body)) :
    Bounded (field (bodies.map (recursiveField callbacks))) := by
  apply field_bounded
  intro child member
  obtain ⟨body, present, rfl⟩ := List.mem_map.mp member
  exact recursive_bounded callbacks body (accepted body present) (leaves body present)

/-- Arbitrarily many compiled recursive children retain distinct candidate positions. -/
theorem recursive_choices_unique [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (bodies : List (RecursiveTermAlignment.Recipe Root Symbol Root))
    (accepted : ∀ body ∈ bodies, RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (bounded : ∀ body ∈ bodies, LeavesBounded (compile callbacks body))
    (distinct : ∀ body ∈ bodies, LeavesDistinct (compile callbacks body)) :
    Unique (field (bodies.map (recursiveField callbacks))) := by
  apply field_unique
  · intro child member
    obtain ⟨body, present, rfl⟩ := List.mem_map.mp member
    exact recursive_bounded callbacks body (accepted body present) (bounded body present)
  · intro child member
    obtain ⟨body, present, rfl⟩ := List.mem_map.mp member
    exact recursive_unique callbacks body (accepted body present) (bounded body present) (distinct body present)

end MicroCFTA.RecursiveNaryChoice
