import MicroCFTA.SourceSizedGroupedIndex
import MicroCFTA.TablePosition

/-!
# Ordered row candidates for grouped source ranking

The source choice offset includes every preceding row count. A failed row
attempt removes that row's candidate. It does not remove its count from a
later candidate's offset. Repeated map insertion keeps the last successful
candidate for the same state.

The row count fields and position attempts remain independent. Local row
replay and completeness laws compose with the actual ordered class lists.
These are internal composition laws. They do not assume a completed public
rank worker. Native candidate buckets, map storage, and the full bottom-up
worker remain separate. No inverse below searches a class list.
-/
namespace MicroCFTA.SourceSizedGroupedRankDispatch
open Language RecursiveSize SizedRank
open RecursiveJoinFields (ValueIndex)

variable {Branch Value : Type}

/-- Add all preceding source row counts at the candidate's requested size. -/
def offsetRows (counts : Branch → Nat → Nat) (before : List Branch) (position : Position) : Position :=
  ⟨position.size, (before.map (fun row => counts row position.size)).sum + position.rank⟩

/-- List successful row attempts in source order with their full choice offsets. -/
def rowCandidates (counts : Branch → Nat → Nat) (attempt : Branch → Option Position) :
    List Branch → List Position
  | [] => []
  | row :: rows =>
      (attempt row).toList ++ (rowCandidates counts attempt rows).map
        (fun position => ⟨position.size, counts row position.size + position.rank⟩)

/-- Retain the last successful source row attempt and add every preceding count. -/
def rowPosition (counts : Branch → Nat → Nat) (attempt : Branch → Option Position) :
    List Branch → Option Position
  | [] => none
  | row :: rows =>
      match rowPosition counts attempt rows with
      | some position => some ⟨position.size, counts row position.size + position.rank⟩
      | none => attempt row

/-- Prefix offsets compose in the same order as source choice branches. -/
theorem offsetRows_append (counts : Branch → Nat → Nat) (before after : List Branch) (position : Position) :
    offsetRows counts (before ++ after) position = offsetRows counts before (offsetRows counts after position) := by
  simp [offsetRows, List.map_append, List.sum_append, Nat.add_assoc]

/-- A branch's source ChoiceIndex is the length of its preceding row prefix. -/
theorem offsetRows_choicePosition (counts : Branch → Nat → Nat)
    (before after : List Branch) (position : Position) :
    (offsetRows counts before position).rank =
      choicePosition ((before ++ after).map fun row => counts row position.size) before.length position.rank := by
  simp [offsetRows, choicePosition]

/-- Actual row index fields give the literal choicePosition count vector. -/
theorem offsetRows_source (indexes : Branch → ValueIndex Value)
    (before after : List Branch) (position : Position) :
    (offsetRows (fun row size => (indexes row).counts size) before position).rank =
      choicePosition (((before ++ after).map indexes).map fun index => index.counts position.size)
        before.length position.rank := by
  simpa only [List.map_map, Function.comp_def] using
    offsetRows_choicePosition (fun row size => (indexes row).counts size) before after position

/-- Splitting stored source rows retains their complete prefix choice offsets. -/
theorem rowCandidates_append (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (before after : List Branch) :
    rowCandidates counts attempt (before ++ after) = rowCandidates counts attempt before ++
      (rowCandidates counts attempt after).map (offsetRows counts before) := by
  induction before with
  | nil =>
      have same : offsetRows counts [] = id := by funext position; cases position; simp [offsetRows]
      simp [rowCandidates, same]
  | cons row before ih =>
      simp only [List.cons_append, rowCandidates, ih, List.map_append, List.append_assoc,
        List.map_map, Function.comp_def, offsetRows]
      congr 2
      apply List.map_congr_left
      intro position _
      simp [offsetRows, Nat.add_assoc]

/-- A concrete successful occurrence emits its source prefix-offset candidate. -/
theorem rowCandidates_member (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (before : List Branch) (row : Branch) (after : List Branch) (position : Position)
    (found : attempt row = some position) :
    offsetRows counts before position ∈ rowCandidates counts attempt (before ++ row :: after) := by
  rw [rowCandidates_append]
  apply List.mem_append.mpr
  right
  apply List.mem_map.mpr
  refine ⟨position, ?_, rfl⟩
  simp [rowCandidates, found]

/-- Every emitted candidate comes from an actual stored row occurrence. -/
theorem rowCandidates_origin (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (rows : List Branch) (position : Position) (member : position ∈ rowCandidates counts attempt rows) :
    ∃ before row after inner, rows = before ++ row :: after ∧ attempt row = some inner ∧
      position = offsetRows counts before inner := by
  induction rows generalizing position with
  | nil => cases member
  | cons first rows ih =>
      rcases List.mem_append.mp member with here | later
      · cases read : attempt first with
        | none => simp [read] at here
        | some inner =>
            have same : inner = position := (by simpa [read] using here : position = inner).symm
            subst position
            exact ⟨[], first, rows, inner, rfl, read, by simp [offsetRows]⟩
      · obtain ⟨tail, tailIn, same⟩ := List.mem_map.mp later
        obtain ⟨before, row, after, inner, shape, read, offset⟩ := ih tail tailIn
        refine ⟨first :: before, row, after, inner, ?_, read, ?_⟩
        · simp only [List.cons_append, shape]
        · rw [← same, offset]
          simp [offsetRows, Nat.add_assoc]

/-- Source row lookup is the existing repeated insertion fold over all candidates. -/
theorem rowPosition_lastWrite (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (rows : List Branch) :
    rowPosition counts attempt rows = TablePosition.lastWrite (rowCandidates counts attempt rows) := by
  rw [TablePosition.lastWrite_correct]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [rowCandidates, List.getLast?_append, List.getLast?_map, ← ih]
      cases tail : rowPosition counts attempt rows <;> cases first : attempt row <;>
        simp [rowPosition, tail, first]

/-- The final map-overwrite value is one emitted source candidate. -/
theorem rowPosition_mem (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (rows : List Branch) (position : Position) (found : rowPosition counts attempt rows = some position) :
    position ∈ rowCandidates counts attempt rows := by
  rw [rowPosition_lastWrite, TablePosition.lastWrite_correct] at found
  exact List.mem_of_getLast? found

/-- Every candidate replays its value in the independent complete ordered row class. -/
theorem rowCandidates_replay (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (classes : Branch → Nat → List Value) (value : Value) (rows : List Branch) :
    (∀ row ∈ rows, ∀ size, counts row size = (classes row size).length) →
    (∀ row ∈ rows, ∀ position, attempt row = some position →
      (classes row position.size)[position.rank]? = some value) →
    ∀ position, position ∈ rowCandidates counts attempt rows →
      (rows.flatMap fun row => classes row position.size)[position.rank]? = some value := by
  induction rows with
  | nil => intro _ _ position member; cases member
  | cons first rows ih =>
      intro counted sound position member
      rcases List.mem_append.mp member with here | later
      · cases read : attempt first with
        | none => simp [read] at here
        | some inner =>
            have same : inner = position := (by simpa [read] using here : position = inner).symm
            subst position
            have replay := sound first (by simp) inner read
            have within := (List.getElem?_eq_some_iff.mp replay).1
            rw [List.flatMap_cons, List.getElem?_append_left within]
            exact replay
      · obtain ⟨part, partIn, same⟩ := List.mem_map.mp later
        subst position
        have replay := ih (fun row member => counted row (by simp [member]))
          (fun row member => sound row (by simp [member])) part partIn
        simp only [List.flatMap_cons]
        rw [counted first (by simp), List.getElem?_append_right (by omega)]
        simpa only [Nat.add_sub_cancel_left] using replay

/-- The last successful map write retains the same independent ordered replay law. -/
theorem rowPosition_replay (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (classes : Branch → Nat → List Value) (value : Value) (rows : List Branch)
    (counted : ∀ row ∈ rows, ∀ size, counts row size = (classes row size).length)
    (sound : ∀ row ∈ rows, ∀ position, attempt row = some position →
      (classes row position.size)[position.rank]? = some value)
    (position : Position) (found : rowPosition counts attempt rows = some position) :
    (rows.flatMap fun row => classes row position.size)[position.rank]? = some value :=
  rowCandidates_replay counts attempt classes value rows counted sound position
    (rowPosition_mem counts attempt rows position found)

/-- Any successful row occurrence makes the complete source row lookup succeed. -/
theorem rowPosition_complete (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (rows : List Branch) (row : Branch) (member : row ∈ rows) (position : Position)
    (found : attempt row = some position) : ∃ result, rowPosition counts attempt rows = some result := by
  induction rows with
  | nil => cases member
  | cons first rows ih =>
      cases tail : rowPosition counts attempt rows with
      | some part =>
          exact ⟨⟨part.size, counts first part.size + part.rank⟩, by simp [rowPosition, tail]⟩
      | none =>
          rcases List.mem_cons.mp member with same | later
          · subst row
            exact ⟨position, by simp [rowPosition, tail, found]⟩
          · obtain ⟨result, computed⟩ := ih later
            rw [tail] at computed
            cases computed

/-- Local row completeness covers every value in the independently ordered choice. -/
theorem rowPosition_exists (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (classes : Branch → Nat → List Value) (value : Value) (rows : List Branch)
    (complete : ∀ row ∈ rows, ∀ size, value ∈ classes row size → ∃ position, attempt row = some position)
    (size : Nat) (member : value ∈ rows.flatMap fun row => classes row size) :
    ∃ position, rowPosition counts attempt rows = some position := by
  obtain ⟨row, rowIn, produced⟩ := List.mem_flatMap.mp member
  obtain ⟨position, found⟩ := complete row rowIn size produced
  exact rowPosition_complete counts attempt rows row rowIn position found

/-- Row replay and completeness characterize exactly when the source lookup succeeds. -/
theorem rowPosition_exists_iff (counts : Branch → Nat → Nat) (attempt : Branch → Option Position)
    (classes : Branch → Nat → List Value) (value : Value) (rows : List Branch)
    (counted : ∀ row ∈ rows, ∀ size, counts row size = (classes row size).length)
    (sound : ∀ row ∈ rows, ∀ position, attempt row = some position →
      (classes row position.size)[position.rank]? = some value)
    (complete : ∀ row ∈ rows, ∀ size, value ∈ classes row size → ∃ position, attempt row = some position) :
    (∃ position, rowPosition counts attempt rows = some position) ↔
      ∃ size, value ∈ rows.flatMap fun row => classes row size := by
  constructor
  · rintro ⟨position, found⟩
    exact ⟨position.size, List.mem_of_getElem?
      (rowPosition_replay counts attempt classes value rows counted sound position found)⟩
  · rintro ⟨size, member⟩
    exact rowPosition_exists counts attempt classes value rows complete size member

/-- The independent actual choice selector replays the source's final row rank. -/
theorem rowPosition_select (indexes : Branch → ValueIndex Value) (attempt : Branch → Option Position)
    (classes : Branch → Nat → List Value) (value : Value) (rows : List Branch)
    (correct : ∀ row ∈ rows, SourceSizedGroupedIndex.Correct (indexes row) (classes row))
    (sound : ∀ row ∈ rows, ∀ position, attempt row = some position →
      (classes row position.size)[position.rank]? = some value)
    (position : Position)
    (found : rowPosition (fun row size => (indexes row).counts size) attempt rows = some position) :
    (SourceSizedGroupedIndex.choiceIndex (rows.map indexes)).select position = some value := by
  have replay := rowPosition_replay (fun row size => (indexes row).counts size) attempt classes value rows
    (fun row member => (correct row member).counts) sound position found
  have choice := SourceSizedGroupedIndex.choice_correct rows indexes classes correct
  have within : position.rank < (SourceSizedGroupedIndex.choiceIndex (rows.map indexes)).counts position.size := by
    rw [choice.counts]
    exact (List.getElem?_eq_some_iff.mp replay).1
  exact (choice.select position within).trans replay

end MicroCFTA.SourceSizedGroupedRankDispatch
