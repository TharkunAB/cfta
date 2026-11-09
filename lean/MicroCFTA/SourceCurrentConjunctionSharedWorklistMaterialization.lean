import MicroCFTA.SourceCurrentConjunctionSharedWorklistFrame
import MicroCFTA.SourceCurrentConjunctionSharedWorklistHandleValidity

/-!
# Pure cached-table materialization

The reader inspects only completed requirement and row-spine cells. It never
executes a projection, equality fold, or worklist step. Missing or unfinished
cells return none. Its private recursion uses the stored tail credit. The
original caller does not supply another execution allowance.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterialization
open InternedConstructorTemplates (Value)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "CellLookup" => SourceCurrentConjunctionRequirementCells.lookup
local notation "SpineLookup" => SourceCurrentConjunctionRequirementRows.lookupSpine
local notation "OldTable" => SourceCurrentConjunctionWorker.Table Symbol Formula

/-- Read one cached requirement without forcing a column or projection cursor. -/
def readCell (handle : Nat) (before : Storage) : Option (List Node) :=
  match CellLookup handle before.requirements with
  | some (.done nodes) => some nodes
  | _ => none

/-- Read the requirement handles in the exact stored row order. -/
def readRow (handles : List Nat) (before : Storage) : Option (List (List Node)) :=
  handles.mapM fun handle => readCell handle before

private def readRowsAt (credits : List Nat) (before : Storage) (credit handle : Nat) :
    Option (List (List (List Node))) :=
  match SpineLookup handle before with
  | some (.done none) => some []
  | some (.done (some (handles, tail))) => do
      let row ← readRow handles before
      let next ← credits[tail]?
      if _smaller : next < credit then
        let rows ← readRowsAt credits before next tail
        some (row :: rows)
      else none
  | _ => none
termination_by credit
decreasing_by exact _smaller

/-- Read a cached row stream with the internally stored original credit. -/
def readRows (credits : List Nat) (handle : Nat) (before : Storage) :
    Option (List (List (List Node))) := do
  let credit ← credits[handle]?
  readRowsAt credits before credit handle

/-- Read the exact stored table order without changing any private or physical state. -/
def readTable (credits : List Nat) (before : WorkState) : Option OldTable :=
  before.table.mapM fun entry => do
    let rows ← match entry.rows with
      | none => some []
      | some handle => readRows credits handle before.storage
    some ⟨entry.nodes, rows⟩

/-- Every requirement handle is present as a completed cached cell. -/
def CellsCached (before : Storage) : Prop :=
  ∀ handle cell, CellLookup handle before.requirements = some cell →
    ∃ nodes, cell = .done nodes

/-- Every row-spine handle is present as a completed cached head. -/
def SpinesCached (before : Storage) : Prop :=
  ∀ handle spine, SpineLookup handle before = some spine →
    ∃ row, spine = .done row

/-- A cached requirement returns its identical stored canonical nodes. -/
theorem readCell_done (handle : Nat) (before : Storage) (nodes : List Node)
    (found : CellLookup handle before.requirements = some (.done nodes)) :
    readCell handle before = some nodes := by
  simp only [readCell, found]

/-- An unfinished projection cursor is not executed by materialization. -/
theorem readCell_pending (handle : Nat) (before : Storage)
    (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula)
    (found : CellLookup handle before.requirements = some (.pending cursor)) :
    readCell handle before = none := by
  simp only [readCell, found]

/-- An unforced pure column is not silently evaluated by materialization. -/
theorem readCell_column (handle : Nat) (before : Storage) (nodes : List Node)
    (found : CellLookup handle before.requirements = some (.column nodes)) :
    readCell handle before = none := by
  simp only [readCell, found]

/-- Every finite row of valid cached handles can be read in full. -/
theorem readRow_complete (handles : List Nat) (before : Storage) (cached : CellsCached before)
    (present : ∀ handle ∈ handles, handle < before.requirements.cells.length) :
    ∃ row, readRow handles before = some row := by
  induction handles with
  | nil => exact ⟨[], rfl⟩
  | cons handle rest ih =>
      have inside := present handle List.mem_cons_self
      have found : CellLookup handle before.requirements = some (before.requirements.cells[handle]) := by
        exact List.getElem?_eq_getElem inside
      obtain ⟨nodes, done⟩ := cached handle _ found
      obtain ⟨row, tail⟩ := ih (fun next member => present next (List.mem_cons_of_mem _ member))
      refine ⟨nodes :: row, ?_⟩
      rw [readRow, List.mapM_cons]
      change (readCell handle before).bind (fun first =>
        (readRow rest before).bind (fun last => some (first :: last))) = some (nodes :: row)
      rw [readCell_done handle before nodes (done ▸ found)]
      change (readRow rest before).bind (fun last => some (nodes :: last)) = some (nodes :: row)
      rw [tail]
      rfl

private theorem readRowsAt_complete (credits : List Nat) (before : Storage)
    (creditValid : SourceCurrentConjunctionRequirementRowsOrigins.Credits credits before)
    (cellsCached : CellsCached before) (spinesCached : SpinesCached before)
    (rowValid : SourceCurrentConjunctionSharedWorklistHandleValidity.RowCells before)
    (credit : Nat) : ∀ handle, credits[handle]? = some credit →
      handle < before.spines.length → ∃ rows, readRowsAt credits before credit handle = some rows := by
  induction credit using Nat.strongRecOn with
  | ind credit ih =>
      intro handle own present
      have found : SpineLookup handle before = some before.spines[handle] :=
        List.getElem?_eq_getElem present
      obtain ⟨row, done⟩ := spinesCached handle _ found
      rw [done] at found
      cases row with
      | none =>
          exact ⟨[], by rw [readRowsAt, found]⟩
      | some row =>
          obtain ⟨handles, tail⟩ := row
          have valid := rowValid _ (List.mem_of_getElem? found)
          change ∀ handle ∈ handles, handle < before.requirements.cells.length at valid
          obtain ⟨row, rowFound⟩ := readRow_complete handles before cellsCached valid
          obtain ⟨old, next, oldFound, nextFound, smaller, tailPresent⟩ :=
            SourceCurrentConjunctionRequirementRowsOrigins.cached_tail creditValid handle tail handles found
          have same : old = credit := Option.some.inj (oldFound.symm.trans own)
          subst old
          obtain ⟨rows, rowsFound⟩ := ih next smaller tail nextFound tailPresent
          refine ⟨row :: rows, ?_⟩
          rw [readRowsAt, found]
          simp [rowFound, nextFound, smaller, rowsFound]

/-- Derived credits and valid completed cells make each present row stream readable. -/
theorem readRows_complete (credits : List Nat) (handle : Nat) (before : Storage)
    (creditValid : SourceCurrentConjunctionRequirementRowsOrigins.Credits credits before)
    (cellsCached : CellsCached before) (spinesCached : SpinesCached before)
    (rowValid : SourceCurrentConjunctionSharedWorklistHandleValidity.RowCells before)
    (present : handle < before.spines.length) :
    ∃ rows, readRows credits handle before = some rows := by
  have inside : handle < credits.length := by rw [creditValid.length]; exact present
  have own := List.getElem?_eq_getElem inside
  obtain ⟨rows, found⟩ := readRowsAt_complete credits before creditValid cellsCached spinesCached
    rowValid credits[handle] handle own present
  refine ⟨rows, ?_⟩
  simp only [readRows, own]
  exact found

/-- One reader step exposes only its actual cached cells and strict stored tail credit. -/
theorem readRows_eq (credits : List Nat) (handle : Nat) (before : Storage) :
    readRows credits handle before =
      match credits[handle]? with
      | none => none
      | some credit =>
          match SpineLookup handle before with
          | some (.done none) => some []
          | some (.done (some (handles, tail))) =>
              (readRow handles before).bind fun row =>
                (credits[tail]?).bind fun next =>
                  if next < credit then
                    (readRows credits tail before).map (fun rows => row :: rows)
                  else none
          | _ => none := by
  cases own : credits[handle]? with
  | none => simp [readRows, own]
  | some credit =>
      rw [readRows, own]
      change readRowsAt credits before credit handle = _
      rw [readRowsAt]
      cases cached : SpineLookup handle before with
      | none => rfl
      | some spine =>
          cases spine with
          | pending tuples => rfl
          | done cachedRow =>
              cases cachedRow with
              | none => rfl
              | some pair =>
                  rcases pair with ⟨handles, tail⟩
                  dsimp only
                  cases row : readRow handles before with
                  | none => simp_all
                  | some values =>
                      cases nextFound : credits[tail]? with
                      | none => simp_all
                      | some next =>
                          by_cases smaller : next < credit
                          · simp_all [readRows]
                            cases readRowsAt credits before next tail <;> rfl
                          · simp_all
                            simp only [ite_eq_right (Nat.not_lt.mpr smaller)]

end MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterialization
