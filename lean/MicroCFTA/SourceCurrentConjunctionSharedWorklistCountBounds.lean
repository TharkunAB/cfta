import MicroCFTA.SourceCurrentConjunctionRequirementRowsNumericControl
import MicroCFTA.SourceCurrentConjunctionSharedWorklistNumericControl
import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues
import MicroCFTA.SourceCurrentConjunctionRequirementCellsFrame

/-!
# Current count bounds for an actual shared worklist transition

Sampling changes no requirement cells and adds only an unforced spine.
Forcing retains the cell count and cannot increase stored cell size.
Row preparation can append one bounded descriptor batch. These actual
branches bound the next queue and table from current counts. No future
state profile or completed callback is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistCountBounds
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistNumericControl (queueSize taskSize)
open SourceCurrentConjunctionRequirementRowsNumericControl (cachedSize freshSize RawWidths)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- One current scalar bounds the private counts and stored descriptor sizes. -/
structure Counts (scalar : Nat) (before : WorkState) : Prop where
  cellCount : before.storage.requirements.cells.length ≤ scalar
  stateSize : SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements ≤ scalar
  cachedSize : SourceCurrentConjunctionRequirementRowsNumericControl.cachedSize before.storage ≤ scalar
  queueSize : SourceCurrentConjunctionSharedWorklistNumericControl.queueSize before.pending ≤ scalar
  tableCount : before.table.length ≤ scalar

/-- A larger scalar retains the same current private bounds. -/
theorem Counts.mono {first last : Nat} {before : WorkState} (increase : first ≤ last)
    (counts : Counts first before) : Counts last before :=
  ⟨Nat.le_trans counts.cellCount increase, Nat.le_trans counts.stateSize increase,
    Nat.le_trans counts.cachedSize increase, Nat.le_trans counts.queueSize increase,
    Nat.le_trans counts.tableCount increase⟩

/-- Empty private storage and the single initial task need only one count unit. -/
theorem initial_counts (budget : Nat) (query : Node) (before : Physical) :
    Counts 1 (initial budget query before) :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.le_refl _, Nat.zero_le _⟩

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem visit_counts (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : WorkState) :
    (visit h nodes rest before).state.storage.requirements.cells = before.storage.requirements.cells ∧
      cachedSize (visit h nodes rest before).state.storage = cachedSize before.storage ∧
      queueSize (visit h nodes rest before).state.pending ≤ queueSize rest + 1 ∧
      (visit h nodes rest before).state.table.length ≤ before.table.length + 1 := by
  cases empty : nodes.any isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty]
      exact ⟨rfl, rfl, Nat.le_succ _, Nat.le_succ _⟩
  | false =>
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
          before.budget (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty skipped]
          exact ⟨rfl, rfl, Nat.le_succ _, Nat.le_succ _⟩
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty skipped sampled]
              refine ⟨rfl, rfl, ?_, Nat.le_succ _⟩
              change 1 + queueSize rest ≤ queueSize rest + 1
              omega
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  rw [visit_overflow h nodes rest before physical tuples cursor empty skipped sampled]
                  exact ⟨rfl, rfl, Nat.le_succ _, Nat.le_succ _⟩
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty skipped sampled]
                      exact ⟨rfl, rfl, Nat.le_succ _, Nat.le_refl _⟩
                  | cons tuple tuples =>
                      rw [visit_positive h nodes rest before physical tuple tuples empty skipped sampled]
                      refine ⟨rfl, ?_, ?_, Nat.le_refl _⟩
                      · exact SourceCurrentConjunctionRequirementRowsNumericControl.cachedSize_allocate_pending
                          (tuple :: tuples) (withPhysical before physical).storage
                      · change 1 + queueSize rest ≤ queueSize rest + 1
                        omega

/-- A successful actual step bounds every private count from the current scalar and guard carrier. -/
theorem step_bounds (alphabet : List Guard) (scalar p h : Nat) (before : WorkState)
    (event : Event) (after : WorkState)
    (values : SourceCurrentConjunctionSharedWorklistValues.Invariant before)
    (widths : RawWidths scalar before.storage)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
      before.storage.requirements.physical.heap)
    (fits : Fits scalar before.storage.requirements.physical.heap)
    (counts : Counts scalar before) (actual : step p h before = .done event after) :
    after.storage.requirements.cells.length ≤ 2 * scalar + shapeThrough alphabet scalar ∧
      SourceCurrentConjunctionRequirementCellsSize.stateSize after.storage.requirements ≤
        max scalar (freshSize alphabet scalar scalar) ∧
      cachedSize after.storage ≤ max scalar (scalar + shapeThrough alphabet scalar) ∧
      queueSize after.pending ≤ 2 * scalar + shapeThrough alphabet scalar + 1 ∧
      after.table.length ≤ scalar + 1 := by
  have retained : ∀ reached : WorkState,
      reached.storage.requirements.cells.length ≤ scalar →
      SourceCurrentConjunctionRequirementCellsSize.stateSize reached.storage.requirements ≤ scalar →
      cachedSize reached.storage ≤ scalar → queueSize reached.pending ≤ scalar →
      reached.table.length ≤ scalar + 1 →
      reached.storage.requirements.cells.length ≤ 2 * scalar + shapeThrough alphabet scalar ∧
        SourceCurrentConjunctionRequirementCellsSize.stateSize reached.storage.requirements ≤
          max scalar (freshSize alphabet scalar scalar) ∧
        cachedSize reached.storage ≤ max scalar (scalar + shapeThrough alphabet scalar) ∧
        queueSize reached.pending ≤ 2 * scalar + shapeThrough alphabet scalar + 1 ∧
        reached.table.length ≤ scalar + 1 := by
    intro reached cellCount stateSize cached queue table
    exact ⟨by omega, Nat.le_trans stateSize (Nat.le_max_left _ _),
      Nat.le_trans cached (Nat.le_max_left _ _), by omega, table⟩
  cases pending : before.pending with
  | nil =>
      rw [step_nil p h before pending] at actual
      cases actual
      exact retained before counts.cellCount counts.stateSize counts.cachedSize counts.queueSize
        (Nat.le_trans counts.tableCount (Nat.le_succ _))
  | cons task rest =>
      cases task with
      | nodes nodes =>
          rw [step_nodes p h before nodes rest pending] at actual
          have stats := visit_counts h nodes rest before
          rw [actual] at stats
          simp only [Outcome.state] at stats
          obtain ⟨cellsSame, cachedSame, queueBound, tableBound⟩ := stats
          apply retained after
          · change after.storage.requirements.cells.length ≤ scalar
            rw [cellsSame]
            exact counts.cellCount
          · unfold SourceCurrentConjunctionRequirementCellsSize.stateSize
            rw [cellsSame]
            exact counts.stateSize
          · rw [cachedSame]
            exact counts.cachedSize
          · have old := counts.queueSize
            rw [pending] at old
            change 1 + queueSize rest ≤ scalar at old
            change queueSize after.pending ≤ queueSize rest + 1 at queueBound
            omega
          · have old := counts.tableCount
            exact Nat.le_trans tableBound (Nat.add_le_add_right old 1)
      | requirements handles =>
          cases handles with
          | nil =>
              rw [step_requirements_nil p h before rest pending] at actual
              cases actual
              apply retained {before with pending := rest} counts.cellCount counts.stateSize counts.cachedSize
              · have old := counts.queueSize
                rw [pending] at old
                change 1 + queueSize rest ≤ scalar at old
                change queueSize rest ≤ scalar
                omega
              · exact Nat.le_trans counts.tableCount (Nat.le_succ _)
          | cons handle handles =>
              cases forced : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
              | failed fault cells =>
                  rw [step_requirement_failed p h handle handles before rest fault cells pending forced] at actual
                  cases actual
              | done nodes cells =>
                  rw [step_requirement_done p h handle handles before rest nodes cells pending forced] at actual
                  have cellLength := SourceCurrentConjunctionRequirementCellsFrame.force_length p h handle before.storage.requirements
                  rw [forced] at cellLength
                  change cells.cells.length = before.storage.requirements.cells.length at cellLength
                  have cellSize := SourceCurrentConjunctionRequirementCellsSize.force_size p h handle before.storage.requirements
                  rw [forced] at cellSize
                  change SourceCurrentConjunctionRequirementCellsSize.stateSize cells ≤
                    SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements at cellSize
                  have stats := visit_counts h nodes (.requirements handles :: rest)
                    {before with storage := {before.storage with requirements := cells}}
                  rw [actual] at stats
                  simp only [Outcome.state] at stats
                  obtain ⟨cellsSame, cachedSame, queueBound, tableBound⟩ := stats
                  change after.storage.requirements.cells = cells.cells at cellsSame
                  change cachedSize after.storage = cachedSize before.storage at cachedSame
                  change after.table.length ≤ before.table.length + 1 at tableBound
                  apply retained after
                  · rw [cellsSame, cellLength]
                    exact counts.cellCount
                  · unfold SourceCurrentConjunctionRequirementCellsSize.stateSize
                    rw [cellsSame]
                    exact Nat.le_trans cellSize counts.stateSize
                  · rw [cachedSame]
                    exact counts.cachedSize
                  · have old := counts.queueSize
                    rw [pending] at old
                    change (handle :: handles).length + 1 + queueSize rest ≤ scalar at old
                    change queueSize after.pending ≤ handles.length + 1 + queueSize rest + 1 at queueBound
                    simp only [List.length_cons] at old
                    omega
                  · exact Nat.le_trans tableBound (Nat.add_le_add_right counts.tableCount 1)
      | rows handle =>
          have bounded := SourceCurrentConjunctionRequirementRowsNumericControl.nextRow_bound
            handle before.storage alphabet scalar scalar values.ready values.raw widths known fits
          cases advanced : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
          | failed fault storage =>
              rw [step_rows_failed p h handle before rest fault storage pending advanced] at actual
              cases actual
          | done row storage =>
              rw [advanced] at bounded
              change storage.requirements.cells.length ≤ before.storage.requirements.cells.length + scalar +
                  shapeThrough alphabet scalar ∧
                SourceCurrentConjunctionRequirementCellsSize.stateSize storage.requirements ≤
                  max (SourceCurrentConjunctionRequirementCellsSize.stateSize before.storage.requirements)
                    (freshSize alphabet scalar scalar) ∧
                RawWidths scalar storage ∧ cachedSize storage ≤
                  max (cachedSize before.storage) (scalar + shapeThrough alphabet scalar) ∧
                SourceCurrentConjunctionRequirementRowsNumericControl.ReturnedWidth
                  (max (cachedSize before.storage) (scalar + shapeThrough alphabet scalar)) (.done row storage) at bounded
              have cellCount : storage.requirements.cells.length ≤ 2 * scalar + shapeThrough alphabet scalar := by
                have old := counts.cellCount
                have added := bounded.1
                omega
              have stateSize := Nat.le_trans bounded.2.1
                (Nat.max_le.mpr ⟨Nat.le_trans counts.stateSize (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
              have cached := Nat.le_trans bounded.2.2.2.1
                (Nat.max_le.mpr ⟨Nat.le_trans counts.cachedSize (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
              have remaining : 1 + queueSize rest ≤ scalar := by
                have old := counts.queueSize
                simpa only [pending, queueSize, taskSize] using old
              cases row with
              | none =>
                  rw [step_rows_none p h handle before rest storage pending advanced] at actual
                  cases actual
                  refine ⟨cellCount, stateSize, cached, ?_, ?_⟩
                  · change queueSize rest ≤ 2 * scalar + shapeThrough alphabet scalar + 1
                    omega
                  · exact Nat.le_trans counts.tableCount (Nat.le_succ _)
              | some row =>
                  rcases row with ⟨handles, tail⟩
                  have returned := bounded.2.2.2.2
                  change handles.length ≤ max (cachedSize before.storage) (scalar + shapeThrough alphabet scalar) at returned
                  have handlesBound : handles.length ≤ scalar + shapeThrough alphabet scalar :=
                    Nat.le_trans returned (Nat.max_le.mpr ⟨by have old := counts.cachedSize; omega, Nat.le_refl _⟩)
                  rw [step_rows_live p h handle tail before rest handles storage pending advanced] at actual
                  cases actual
                  refine ⟨cellCount, stateSize, cached, ?_, ?_⟩
                  · change handles.length + 1 + (1 + queueSize rest) ≤ 2 * scalar + shapeThrough alphabet scalar + 1
                    omega
                  · exact Nat.le_trans counts.tableCount (Nat.le_succ _)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistCountBounds
