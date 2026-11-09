import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.SourceCurrentConjunctionRequirementCellsClosed

/-!
# Closed captured operands through actual shared rows

Closed tuple children supply closed columns and pending class forests.
Equality folding and descriptor allocation do not project a new value.
Their closedness proofs therefore need no heap-residency premise. Finite
row traversal retains closed cells and every pending raw tuple on successful
and failed outcomes. Physical effects and residency have separate laws.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
open InternedConstructorTemplates (EdgeValue)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementCellsClosed (CellClosed Invariant)
variable {Symbol Formula : Type}
local notation "Row" => EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Every pending raw tuple retains closed child values. -/
def RawClosed : Spine Symbol Formula → Prop
  | .pending tuples => ∀ tuple ∈ tuples, ClosedEdges tuple
  | .done _ => True

/-- Every actual pending spine retains closed raw tuples. -/
def SpineClosed (before : Storage) : Prop :=
  ∀ spine ∈ before.spines, RawClosed spine

/-- Ordered descriptor allocation retains all existing closed cells and new closed operands. -/
theorem allocateCells_closed (cells : List Cell) (before : Cells) (closed : Invariant before)
    (added : ∀ cell ∈ cells, CellClosed cell) : Invariant (allocateCells cells before).2 := by
  induction cells generalizing before with
  | nil => exact closed
  | cons cell rest ih =>
      change Invariant (allocateCells rest (SourceCurrentConjunctionRequirementCells.allocate cell before).2).2
      exact ih _ (SourceCurrentConjunctionRequirementCellsClosed.allocate_closed cell before closed
        (added cell List.mem_cons_self))
        (fun later member => added later (List.mem_cons_of_mem _ member))

/-- Literal columns and class cursors contain only children from the actual closed tuple. -/
theorem descriptors_closed (tuple : List Row) (constraints : EqualityNormalize.Constraints)
    (closed : ClosedEdges tuple) : ∀ cell ∈ descriptors tuple constraints, CellClosed cell := by
  have forests : ∀ forest ∈ tuple.map EdgeValue.children, ClosedValues forest := by
    intro forest member
    obtain ⟨edge, included, same⟩ := List.mem_map.mp member
    cases same
    exact closed edge included
  intro cell member
  change cell ∈ (SourceCurrentConjunctionRequirements.columns tuple).map _ ++ constraints.map _ at member
  rcases List.mem_append.mp member with column | constraint
  · obtain ⟨nodes, included, same⟩ := List.mem_map.mp column
    cases same
    intro node member
    obtain ⟨forest, forestIn, childIn⟩ := MergedPhysicalGroupEdges.columns_member _ _ nodes included node member
    exact forests forest forestIn node childIn
  · obtain ⟨paths, _, same⟩ := List.mem_map.mp constraint
    cases same
    constructor
    · intro node member
      cases member
    · intro job included
      obtain ⟨forest, forestIn, present⟩ := List.mem_flatMap.mp included
      obtain ⟨path, _, same⟩ := List.mem_map.mp present
      cases same
      exact forests forest forestIn

/-- Every actual tuple preparation outcome retains closed stored cells. -/
theorem prepareTuple_closed (tuple : List Row) (before : Storage)
    (closed : Invariant before.requirements) (tupleClosed : ClosedEdges tuple) :
    Invariant (prepareTuple tuple before).state.requirements := by
  unfold prepareTuple
  dsimp only
  split
  · exact closed
  · exact closed
  · split
    · exact closed
    · let current : Cells := {before.requirements with physical :=
        ⟨before.requirements.physical.heap,
          (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩}
      exact allocateCells_closed _ current closed (descriptors_closed tuple _ tupleClosed)

private theorem spines_same (before after : Storage) (same : after.spines = before.spines)
    (closed : SpineClosed before) : SpineClosed after := by
  intro spine member
  rw [same] at member
  exact closed spine member

private theorem spines_update (handle : Nat) (replacement : Spine Symbol Formula) (before : Storage)
    (closed : SpineClosed before) (own : RawClosed replacement) :
    SpineClosed (updateSpine handle replacement before) := by
  intro spine member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact closed spine old
  · exact same.symm ▸ own

private theorem spines_allocate (tuples : List (List Row)) (before : Storage)
    (closed : SpineClosed before) (own : RawClosed (Spine.pending tuples)) :
    SpineClosed (allocateSpine (.pending tuples) before).2 := by
  intro spine member
  rcases List.mem_append.mp member with old | fresh
  · exact closed spine old
  · have same : spine = .pending tuples := List.mem_singleton.mp fresh
    exact same.symm ▸ own

private theorem pending_closed (handle : Nat) (tuples : List (List Row)) (before : Storage)
    (closed : Invariant before.requirements) (raw : SpineClosed before)
    (found : lookupSpine handle before = some (.pending tuples)) :
    Invariant (nextRow handle before).state.requirements ∧ SpineClosed (nextRow handle before).state := by
  induction tuples generalizing before with
  | nil =>
      rw [nextRow_nil handle before found]
      exact ⟨closed, spines_update handle (.done none) before raw True.intro⟩
  | cons tuple rest ih =>
      have tupleClosed := raw (.pending (tuple :: rest)) (List.mem_of_getElem? found) tuple List.mem_cons_self
      have first := prepareTuple_closed tuple before closed tupleClosed
      have retained := prepareTuple_spines tuple before
      have remaining := spines_same before (prepareTuple tuple before).state retained raw
      cases prepared : prepareTuple tuple before with
      | failed fault after =>
          rw [nextRow_failed handle tuple rest before after fault found prepared]
          simpa only [prepared, Outcome.state] using And.intro first remaining
      | done row after =>
          have current : Invariant after.requirements ∧ SpineClosed after := by
            simpa only [prepared, Outcome.state] using And.intro first remaining
          rw [prepared] at retained
          change after.spines = before.spines at retained
          have present : lookupSpine handle after = some (.pending (tuple :: rest)) := by
            change after.spines[handle]? = some (.pending (tuple :: rest))
            rw [retained]
            exact found
          have suffix : RawClosed (Spine.pending rest) := by
            intro next member
            exact current.2 (.pending (tuple :: rest)) (List.mem_of_getElem? present) next
              (List.mem_cons_of_mem _ member)
          cases row with
          | none =>
              rw [nextRow_rejected handle tuple rest before after found prepared]
              exact ih (updateSpine handle (.pending rest) after) current.1
                (spines_update handle (.pending rest) after current.2 suffix)
                (lookupSpine_update handle (.pending (tuple :: rest)) (.pending rest) after present)
          | some handles =>
              rw [nextRow_live handle tuple rest before after handles found prepared]
              exact ⟨current.1, spines_update handle (.done (some (handles, after.spines.length)))
                (allocateSpine (.pending rest) after).2 (spines_allocate rest after current.2 suffix) True.intro⟩

/-- Every actual row outcome preserves closed stored cells and all pending raw tuples. -/
theorem nextRow_closed (handle : Nat) (before : Storage)
    (closed : Invariant before.requirements) (raw : SpineClosed before) :
    Invariant (nextRow handle before).state.requirements ∧ SpineClosed (nextRow handle before).state := by
  cases found : lookupSpine handle before with
  | none => rw [nextRow_missing handle before found]; exact ⟨closed, raw⟩
  | some spine =>
      cases spine with
      | done row => rw [nextRow_hit handle row before found]; exact ⟨closed, raw⟩
      | pending tuples => exact pending_closed handle tuples before closed raw found

end MicroCFTA.SourceCurrentConjunctionRequirementRowsClosed
