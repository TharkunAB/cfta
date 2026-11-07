import MicroCFTA.SourceSizedGroupedRankPrefixes
import MicroCFTA.SourceSizedConjunctionSemantics

/-!
# Representative child positions in grouped transition ranking

The nonempty equality branch reads the first child of each source group.
Valid direct-child classes make each read valid. The source equality check
makes reconstruction recover the original children. Cached source prefix
fields then replay the original transition term at its computed rank.

The child position and field laws are internal induction inputs. Candidate
lookup, the recursive bottom-up worker and native map storage are separate.
-/
namespace MicroCFTA.SourceSizedGroupedRankLeaders
open Language RecursiveSize SizedRank CompactGroups CompactEdgeRanks
open SourceSizedGroupedChainOrder
open RecursiveJoinFields (ValueIndex)

variable {State Symbol : Type}

/-- Read the term at each nonempty group's first child. -/
def leaderValues (values : List (Term Symbol)) (groups : List (List Nat)) : List (Term Symbol) :=
  groups.filterMap fun group => group.head?.bind fun first => values[first]?

/-- Read the representative position and multiply its size by the group length. -/
def leaderPositions (positions : List Position) (groups : List (List Nat)) : List Position :=
  groups.filterMap fun group => group.head?.bind fun first =>
    (positions[first]?).map (SourceSizedGroupedPositions.scalePosition group.length)

/-- Replayed child states, terms and positions have the same lengths. -/
theorem positioned_lengths (classes : State → Nat → List (Term Symbol))
    (children : List State) (values : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classes state size) children values positions) :
    children.length = values.length ∧ children.length = positions.length := by
  induction positioned with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

/-- An actual in-range child lookup retains its state, term and replayed position. -/
theorem positioned_at (classes : State → Nat → List (Term Symbol))
    (children : List State) (values : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classes state size) children values positions)
    (index : Nat) (within : index < children.length) :
    ∃ state term position, children[index]? = some state ∧ values[index]? = some term ∧
      positions[index]? = some position ∧ (classes state position.size)[position.rank]? = some term := by
  induction positioned generalizing index with
  | nil => simp at within
  | @cons state term states terms positions position replay rest ih =>
      cases index with
      | zero => exact ⟨state, term, position, rfl, rfl, rfl, replay⟩
      | succ index =>
          obtain ⟨state, term, position, read, valueRead, positionRead, replay⟩ := ih index (by simpa using within)
          exact ⟨state, term, position, by simpa using read, by simpa using valueRead,
            by simpa using positionRead, replay⟩

/-- Source representative reads provide replayed positions for all nonempty bounded groups. -/
theorem leaders_positioned (classes : State → Nat → List (Term Symbol))
    (children : List State) (values : List (Term Symbol)) (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classes state size) children values positions)
    (groups : List (List Nat)) (nonempty : ∀ group ∈ groups, group ≠ [])
    (bounded : ∀ group ∈ groups, ∀ index ∈ group, index < children.length) :
    TablePosition.Positioned (fun size group => groupClass classes children group size)
      groups (leaderValues values groups) (leaderPositions positions groups) := by
  revert nonempty bounded
  induction groups with
  | nil => intro _ _; exact .nil
  | cons group groups ih =>
      intro nonempty bounded
      have present : group ∈ group :: groups := by simp
      cases group with
      | nil => exact False.elim (nonempty [] present rfl)
      | cons first rest =>
          obtain ⟨state, term, position, read, valueRead, positionRead, replay⟩ :=
            positioned_at classes children values positions positioned first (bounded _ present first (by simp))
          simp only [leaderValues, leaderPositions, List.filterMap_cons, List.head?_cons,
            Option.bind_some, valueRead, positionRead, Option.map_some]
          exact .cons (SourceSizedGroupedPositions.groupPosition_replay classes children first rest
            state read position term replay)
            (ih (fun group member => nonempty group (by simp [member]))
              (fun group member => bounded group (by simp [member])))

private theorem selected_agree (symbol : Symbol) (values : List (Term Symbol))
    (groups : List (List Nat)) (nonempty : ∀ group ∈ groups, group ≠ [])
    (bounded : ∀ group ∈ groups, ∀ index ∈ group, index < values.length)
    (equal : GroupsEqual (childValue (.node symbol []) values) groups) :
    (leaderValues values groups).length = groups.length ∧
      CompactChildSlots.Agrees (childValue (.node symbol []) values) (groups.zip (leaderValues values groups)) := by
  revert nonempty bounded equal
  induction groups with
  | nil => intro _ _ _; exact ⟨rfl, by simp [CompactChildSlots.Agrees, leaderValues]⟩
  | cons group groups ih =>
      intro nonempty bounded equal
      have present : group ∈ group :: groups := by simp
      cases group with
      | nil => exact False.elim (nonempty [] present rfl)
      | cons first rest =>
          have within := bounded _ present first (by simp)
          have read : values[first]? = some values[first] := List.getElem?_eq_getElem within
          obtain ⟨length, agrees⟩ := ih
            (fun group member => nonempty group (by simp [member]))
            (fun group member => bounded group (by simp [member]))
            (fun group member => equal group (by simp [member]))
          have leaders : leaderValues values ((first :: rest) :: groups) =
              values[first] :: leaderValues values groups := by
            simp only [leaderValues, List.filterMap_cons, List.head?_cons, Option.bind_some, read]
          rw [leaders]
          refine ⟨by simp [length], ?_⟩
          intro pair member index inPair
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact (equal _ present index inPair first (by simp)).trans (by simp [childValue, read])
          · exact agrees pair later index inPair

/-- Equality-checked representative values reconstruct every original child in order. -/
theorem assemble_leaders [DecidableEq Symbol] (symbol : Symbol) (values : List (Term Symbol))
    (classes : List (List Nat)) (valid : ValidClasses values.length classes)
    (held : SourceSizedConjunctionSemantics.holds classes (.node symbol values) = true) :
    assemble symbol values.length (childGroups values.length classes)
      (leaderValues values (childGroups values.length classes)) = .node symbol values := by
  let groups := childGroups values.length classes
  have nonempty := childGroups_nonempty values.length classes valid
  have bounded : ∀ group ∈ groups, ∀ index ∈ group, index < values.length := by
    intro group member index present
    exact List.mem_range.mp ((childGroups_positions values.length classes).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, member, present⟩))
  have equal : GroupsEqual (childValue (.node symbol []) values) groups :=
    (childGroups_exact _ values.length classes valid).mpr
      ((SourceSizedConjunctionSemantics.holds_node symbol values classes valid).mp held)
  obtain ⟨length, agrees⟩ := selected_agree symbol values groups nonempty bounded equal
  have layout : (groups.zip (leaderValues values groups)).map Prod.fst = groups :=
    List.map_fst_zip (Nat.le_of_eq length.symm)
  have restored := Option.some.inj ((construct_generated symbol values.length classes _ layout).symm.trans
    (construct_exact symbol (childValue (.node symbol []) values) _ values.length classes layout agrees))
  have original : (List.range values.length).map (childValue (.node symbol []) values) = values := by
    apply List.ext_getElem
    · simp
    · intro index _ within
      simp [childValue, List.getElem?_eq_getElem within]
  exact restored.trans (congrArg (Term.node symbol) original)

/-- The checked representative-child rank with actual cached fields replays the original term. -/
theorem transition_replay [DecidableEq Symbol]
    (indexes : State → ValueIndex (Term Symbol)) (classAt : State → Nat → List (Term Symbol))
    (correct : ∀ state, SourceSizedGroupedIndex.Correct (indexes state) (classAt state))
    (symbol : Symbol) (children : List State) (classes : List (List Nat))
    (valid : ValidClasses children.length classes) (values : List (Term Symbol))
    (positions : List Position)
    (positioned : TablePosition.Positioned (fun size state => classAt state size) children values positions)
    (held : SourceSizedConjunctionSemantics.holds classes (.node symbol values) = true) :
    let groups := childGroups children.length classes
    let result := SourceSizedGroupedRankPrefixes.groupedPosition indexes symbol children classes
      (leaderPositions positions groups)
    (rowClass classAt symbol children classes result.size)[result.rank]? = some (.node symbol values) := by
  have arity := (positioned_lengths classAt children values positions positioned).1
  have nonempty := childGroups_nonempty children.length classes valid
  have bounded : ∀ group ∈ childGroups children.length classes, ∀ index ∈ group, index < children.length := by
    intro group member index present
    exact List.mem_range.mp ((childGroups_positions children.length classes).mem_iff.mp
      (List.mem_flatten.mpr ⟨group, member, present⟩))
  have grouped := leaders_positioned classAt children values positions positioned _ nonempty bounded
  have replay := SourceSizedGroupedRankPrefixes.groupedPosition_replay indexes classAt correct
    symbol children classes _ _ grouped
  have assembled : assemble symbol children.length (childGroups children.length classes)
      (leaderValues values (childGroups children.length classes)) = .node symbol values := by
    rw [arity]
    exact assemble_leaders symbol values classes (by simpa only [← arity] using valid) held
  dsimp only at replay ⊢
  rw [assembled] at replay
  exact replay

end MicroCFTA.SourceSizedGroupedRankLeaders
