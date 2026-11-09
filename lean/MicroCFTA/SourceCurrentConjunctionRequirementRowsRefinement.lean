import MicroCFTA.SourceCurrentConjunctionRequirementCellsRefinement
import MicroCFTA.SourceCurrentConjunctionRequirementRows

/-!
# Literal descriptor origins through row preparation

Allocation appends each original descriptor at its returned handle.
Tuple preparation appends only the descriptors of its actual live classes.
Row forcing skips rejected tuples without adding cells. It appends at most
one literal descriptor batch. Old origins remain the same prefix on every
outcome. These laws do not assert language coverage for a completed table.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement
open InternedConstructorTemplates (EdgeValue)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementCellsRefinement (Invariant)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Row" => EdgeValue Symbol Guard
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

private theorem same_cells {origins : List Cell} {before after : Cells}
    (refined : Invariant origins before) (same : after.cells = before.cells) : Invariant origins after := by
  refine ⟨refined.length.trans (congrArg List.length same).symm, ?_⟩
  intro handle original current originFound currentFound
  apply refined.cells handle original current originFound
  simpa only [SourceCurrentConjunctionRequirementCells.lookup, same] using currentFound

/-- Ordered allocation extends the origins by the identical literal descriptor list. -/
theorem allocateCells_refinement (cells : List Cell) (before : Cells) (origins : List Cell)
    (refined : Invariant origins before) : Invariant (origins ++ cells) (allocateCells cells before).2 := by
  induction cells generalizing before origins with
  | nil => simpa only [allocateCells, List.append_nil] using refined
  | cons cell rest ih =>
      have first := SourceCurrentConjunctionRequirementCellsRefinement.allocate cell before origins refined
      have later := ih (SourceCurrentConjunctionRequirementCells.allocate cell before).2 (origins ++ [cell]) first
      simpa only [allocateCells, List.append_assoc, List.cons_append, List.nil_append] using later

/-- Every returned handle identifies its exact descriptor position in the extended origin list. -/
theorem allocateCells_origin (cells : List Cell) (before : Cells) (origins : List Cell)
    (refined : Invariant origins before) (index : Nat) (cell : Cell) (found : cells[index]? = some cell) :
    (allocateCells cells before).1[index]? = some (before.cells.length + index) ∧
      (origins ++ cells)[before.cells.length + index]? = some cell := by
  constructor
  · rw [allocateCells_handles]
    simpa only [Nat.one_mul] using
      (List.getElem?_range' (s := before.cells.length) (step := 1) (List.getElem?_eq_some_iff.mp found).1)
  · rw [← refined.length, List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa only [Nat.add_sub_cancel_left] using found

/-- A preparation receipt records its actual classes and fresh handle range. -/
def Prepared (tuple : List Row) (before : Storage) (added : List Cell) :
    Outcome Symbol Formula (Option Handles) → Prop
  | .failed _ _ | .done none _ => added = []
  | .done (some handles) _ => ∃ result constraints,
      (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).1 = .ok (some result) ∧
      SourceEqualityInheritedPayload.classes result.payload = some constraints ∧
      added = descriptors tuple constraints ∧
      handles = List.range' before.requirements.cells.length added.length

/-- Actual preparation preserves old origins and records only its literal allocated batch. -/
theorem prepareTuple_refinement (tuple : List Row) (before : Storage) (origins : List Cell)
    (refined : Invariant origins before.requirements) :
    ∃ added, Invariant (origins ++ added) (prepareTuple tuple before).state.requirements ∧
      (prepareTuple tuple before).state.requirements.cells = before.requirements.cells ++ added ∧
      Prepared tuple before added (prepareTuple tuple before) := by
  cases folded : SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality with
  | mk result operations =>
      cases result with
      | error message =>
          simp only [prepareTuple, folded, Outcome.state]
          refine ⟨[], ?_, ?_, rfl⟩
          · simpa only [List.append_nil] using same_cells refined (after :=
              {before.requirements with physical := ⟨before.requirements.physical.heap, operations⟩}) rfl
          · exact (List.append_nil _).symm
      | ok value =>
          cases value with
          | none =>
              simp only [prepareTuple, folded, Outcome.state]
              refine ⟨[], ?_, ?_, rfl⟩
              · simpa only [List.append_nil] using same_cells refined (after :=
                  {before.requirements with physical := ⟨before.requirements.physical.heap, operations⟩}) rfl
              · exact (List.append_nil _).symm
          | some result =>
              cases classes : SourceEqualityInheritedPayload.classes result.payload with
              | none =>
                  simp only [prepareTuple, folded, classes, Outcome.state]
                  refine ⟨[], ?_, ?_, rfl⟩
                  · simpa only [List.append_nil] using same_cells refined (after :=
                      {before.requirements with physical := ⟨before.requirements.physical.heap, operations⟩}) rfl
                  · exact (List.append_nil _).symm
              | some constraints =>
                  let current : Cells := {before.requirements with
                    physical := ⟨before.requirements.physical.heap, operations⟩}
                  have currentRefined : Invariant origins current := same_cells refined rfl
                  have allocated := allocateCells_refinement (descriptors tuple constraints) current origins currentRefined
                  simp only [prepareTuple, folded, classes, Outcome.state]
                  refine ⟨descriptors tuple constraints, allocated, ?_, ?_⟩
                  · exact allocateCells_order _ current
                  · refine ⟨result, constraints, congrArg Prod.fst folded, classes, rfl, ?_⟩
                    exact allocateCells_handles _ current

private theorem pending_refinement (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (origins : List Cell) (refined : Invariant origins before.requirements)
    (found : lookupSpine handle before = some (.pending tuples)) :
    ∃ added, Invariant (origins ++ added) (nextRow handle before).state.requirements ∧
      (nextRow handle before).state.requirements.cells = before.requirements.cells ++ added ∧
      (added = [] ∨ ∃ tuple constraints, added = descriptors tuple constraints) := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      refine ⟨[], ?_, (List.append_nil _).symm, Or.inl rfl⟩
      change Invariant (origins ++ []) before.requirements
      simpa only [List.append_nil] using refined
  | cons tuple rest ih =>
      have first := prepareTuple_refinement tuple before origins refined
      have spines := prepareTuple_spines tuple before
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [prepared] at first
          obtain ⟨added, aligned, appended, empty⟩ := first
          change added = [] at empty
          subst added
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          exact ⟨[], aligned, appended, Or.inl rfl⟩
      | done row after =>
          rw [prepared] at first spines
          obtain ⟨added, aligned, appended, batch⟩ := first
          change after.spines = before.spines at spines
          have present : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [spines]
            exact found
          cases row with
          | none =>
              change added = [] at batch
              subst added
              have unchanged : after.requirements.cells = before.requirements.cells := by
                simpa only [Outcome.state, List.append_nil] using appended
              have current : Invariant origins after.requirements := by
                simpa only [Outcome.state, List.append_nil] using aligned
              have later := ih (updateSpine handle (.pending rest) after) current
                (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after present)
              obtain ⟨added, final, cells, source⟩ := later
              rw [nextRow_rejected handle tuple rest before after found prepared]
              refine ⟨added, final, ?_, source⟩
              simpa only [updateSpine, unchanged] using cells
          | some handles =>
              obtain ⟨_, constraints, _, _, literal, _⟩ := batch
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact ⟨added, aligned, appended, Or.inr ⟨tuple, constraints, literal⟩⟩

/-- A row observation appends no cells or one literal live descriptor batch on every outcome. -/
theorem nextRow_refinement (handle : Nat) (before : Storage) (origins : List Cell)
    (refined : Invariant origins before.requirements) :
    ∃ added, Invariant (origins ++ added) (nextRow handle before).state.requirements ∧
      (nextRow handle before).state.requirements.cells = before.requirements.cells ++ added ∧
      (added = [] ∨ ∃ tuple constraints, added = descriptors tuple constraints) := by
  cases found : lookupSpine handle before with
  | none =>
      rw [nextRow_missing handle before found]
      refine ⟨[], ?_, (List.append_nil _).symm, Or.inl rfl⟩
      change Invariant (origins ++ []) before.requirements
      simpa only [List.append_nil] using refined
  | some spine =>
      cases spine with
      | done row =>
          rw [nextRow_hit handle row before found]
          refine ⟨[], ?_, (List.append_nil _).symm, Or.inl rfl⟩
          change Invariant (origins ++ []) before.requirements
          simpa only [List.append_nil] using refined
      | pending tuples => exact pending_refinement handle tuples before origins refined found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsRefinement
