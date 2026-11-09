import MicroCFTA.SourceCurrentConjunctionRequirementRows

/-!
# Old private lookups through actual row preparation

Requirement allocation appends descriptors without changing older cells.
Row forcing changes only its own old spine and can append one tail.
These laws cover every outcome. They do not force an unused cell or tail.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsFrame
open InternedConstructorTemplates
open SourceCurrentConjunctionRequirementRows

variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Rows" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "cellLookup" => SourceCurrentConjunctionRequirementCells.lookup

/-- Ordered descriptor allocation preserves every present old requirement cell. -/
theorem allocateCells_old (cells : List Cell) (before : Cells) (handle : Nat) (original : Cell)
    (found : cellLookup handle before = some original) :
    cellLookup handle (allocateCells cells before).2 = some original := by
  change (allocateCells cells before).2.cells[handle]? = some original
  rw [allocateCells_order]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Descriptor allocation appends its exact finite number of cells. -/
theorem allocateCells_length (cells : List Cell) (before : Cells) :
    (allocateCells cells before).2.cells.length = before.cells.length + cells.length := by
  simp only [allocateCells_order, List.length_append]

/-- Every tuple outcome preserves each present old requirement cell. -/
theorem prepareTuple_old (tuple : List Row) (before : Rows) (handle : Nat) (original : Cell)
    (found : cellLookup handle before.requirements = some original) :
    cellLookup handle (prepareTuple tuple before).state.requirements = some original := by
  unfold prepareTuple
  dsimp only
  split
  · exact found
  · exact found
  · split
    · exact found
    · exact allocateCells_old _ _ handle original found

/-- A tuple outcome never removes an allocated requirement handle. -/
theorem prepareTuple_cells_le (tuple : List Row) (before : Rows) :
    before.requirements.cells.length ≤ (prepareTuple tuple before).state.requirements.cells.length := by
  unfold prepareTuple
  dsimp only
  split
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · dsimp only [Outcome.state]
      rw [allocateCells_length]
      exact Nat.le_add_right _ _

/-- Tuple preparation preserves the complete spine list. -/
theorem prepareTuple_spines_le (tuple : List Row) (before : Rows) :
    before.spines.length ≤ (prepareTuple tuple before).state.spines.length := by
  simpa only [prepareTuple_spines] using Nat.le_refl before.spines.length

private structure Frame (target : Nat) (before after : Rows) : Prop where
  cells_le : before.requirements.cells.length ≤ after.requirements.cells.length
  spines_le : before.spines.length ≤ after.spines.length
  cells : ∀ handle original, cellLookup handle before.requirements = some original →
    cellLookup handle after.requirements = some original
  spines : ∀ handle original, handle ≠ target → lookupSpine handle before = some original →
    lookupSpine handle after = some original

private theorem frame_refl (target : Nat) (before : Rows) : Frame target before before :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ found => found, fun _ _ _ found => found⟩

private theorem frame_trans {target : Nat} {first middle last : Rows}
    (one : Frame target first middle) (two : Frame target middle last) : Frame target first last :=
  ⟨Nat.le_trans one.cells_le two.cells_le, Nat.le_trans one.spines_le two.spines_le,
    fun handle original found => two.cells handle original (one.cells handle original found),
    fun handle original different found =>
      two.spines handle original different (one.spines handle original different found)⟩

private theorem prepare_frame (target : Nat) (tuple : List Row) (before : Rows) :
    Frame target before (prepareTuple tuple before).state := by
  refine ⟨prepareTuple_cells_le tuple before, prepareTuple_spines_le tuple before,
    prepareTuple_old tuple before, ?_⟩
  intro handle original _ found
  change (prepareTuple tuple before).state.spines[handle]? = some original
  rw [prepareTuple_spines]
  exact found

private theorem update_frame (target : Nat) (replacement : Spine Symbol Formula) (before : Rows) :
    Frame target before (updateSpine target replacement before) := by
  refine ⟨Nat.le_refl _, ?_, fun _ _ found => found, ?_⟩
  · simpa only [updateSpine, List.length_set] using Nat.le_refl before.spines.length
  · intro handle original different found
    change (before.spines.set target replacement)[handle]? = some original
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact found

private theorem allocate_frame (target : Nat) (cell : Spine Symbol Formula) (before : Rows) :
    Frame target before (allocateSpine cell before).2 := by
  refine ⟨Nat.le_refl _, ?_, fun _ _ found => found, ?_⟩
  · change before.spines.length ≤ (before.spines ++ [cell]).length
    simp only [List.length_append, List.length_singleton]
    omega
  · intro handle original _ found
    change (before.spines ++ [cell])[handle]? = some original
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found

private theorem pending_frame (target : Nat) (tuples : List (List Row)) :
    ∀ before : Rows, lookupSpine target before = some (.pending tuples) →
      Frame target before (nextRow target before).state := by
  induction tuples with
  | nil =>
      intro before found
      rw [nextRow_nil target before found]
      exact update_frame target (.done none) before
  | cons tuple rest ih =>
      intro before found
      have head := prepare_frame target tuple before
      cases prepared : prepareTuple tuple before with
      | failed fault current =>
          rw [nextRow_failed target tuple rest before current fault found prepared]
          simpa only [prepared, Outcome.state] using head
      | done row current =>
          have kept : Frame target before current := by
            simpa only [prepared, Outcome.state] using head
          have spines := prepareTuple_spines tuple before
          rw [prepared] at spines
          change current.spines = before.spines at spines
          have currentFound : lookupSpine target current = some (.pending (tuple :: rest)) := by
            change current.spines[target]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          cases row with
          | none =>
              have continued := lookupSpine_update target (.pending (tuple :: rest)) (.pending rest)
                current currentFound
              have tail := ih (updateSpine target (.pending rest) current) continued
              rw [nextRow_rejected target tuple rest before current found prepared]
              exact frame_trans (frame_trans kept (update_frame target (.pending rest) current)) tail
          | some handles =>
              rw [nextRow_live target tuple rest before current handles found prepared]
              exact frame_trans (frame_trans kept (allocate_frame target (.pending rest) current))
                (update_frame target (.done (some (handles, current.spines.length)))
                  (allocateSpine (.pending rest) current).2)

private theorem nextRow_frame (target : Nat) (before : Rows) :
    Frame target before (nextRow target before).state := by
  cases found : lookupSpine target before with
  | none =>
      rw [nextRow_missing target before found]
      exact frame_refl target before
  | some cell =>
      cases cell with
      | done row =>
          rw [nextRow_hit target row before found]
          exact frame_refl target before
      | pending tuples => exact pending_frame target tuples before found

/-- Finite row forcing preserves every present old requirement cell on all outcomes. -/
theorem nextRow_old (target : Nat) (before : Rows) (handle : Nat) (original : Cell)
    (found : cellLookup handle before.requirements = some original) :
    cellLookup handle (nextRow target before).state.requirements = some original :=
  (nextRow_frame target before).cells handle original found

/-- Finite row forcing preserves every other present old spine on all outcomes. -/
theorem nextRow_other (target : Nat) (before : Rows) (handle : Nat) (original : Spine Symbol Formula)
    (different : handle ≠ target) (found : lookupSpine handle before = some original) :
    lookupSpine handle (nextRow target before).state = some original :=
  (nextRow_frame target before).spines handle original different found

/-- Finite row forcing never removes a requirement handle. -/
theorem nextRow_cells_le (target : Nat) (before : Rows) :
    before.requirements.cells.length ≤ (nextRow target before).state.requirements.cells.length :=
  (nextRow_frame target before).cells_le

/-- Finite row forcing never removes a spine handle. -/
theorem nextRow_spines_le (target : Nat) (before : Rows) :
    before.spines.length ≤ (nextRow target before).state.spines.length :=
  (nextRow_frame target before).spines_le

end MicroCFTA.SourceCurrentConjunctionRequirementRowsFrame
