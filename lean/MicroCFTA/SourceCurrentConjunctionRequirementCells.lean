import MicroCFTA.SourceCurrentConjunctionRequirementPull

/-!
# Shared cells for actual requirement projections

Allocation appends one cell and retains all earlier handles. A force step
updates the same cell. Completed cells return without another projection.
A failed projection retains its pending cursor and actual physical state.
The complete force recurses on the cursor's pending jobs. It takes no
additional observation allowance. The selected worklist does not use this
heap yet. Table coverage and terminal materialization remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCells
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Job)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Cursor" => SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula

/-- A cell retains an unforced column, a projection cursor, or its cached value. -/
inductive Cell (Symbol Formula : Type) where
  | column (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
  | pending (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula)
  | done (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))

/-- Cell storage and the native physical state advance together. -/
structure State (Symbol Formula : Type) where
  cells : List (Cell Symbol Formula)
  physical : Physical Symbol Formula

/-- Missing handles and projection faults retain their distinct diagnostics. -/
inductive Fault (Symbol Formula : Type) where
  | missing (handle : Nat)
  | projection (handle : Nat) (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula)
      (observation : SourceCurrentConjunctionRowsWorker.Fault)

/-- Every observation retains the reached cells and physical state. -/
inductive Outcome (Symbol Formula Output : Type) where
  | done (output : Output) (state : State Symbol Formula)
  | failed (fault : Fault Symbol Formula) (state : State Symbol Formula)

/-- A completed observation returns its exact state; a failure retains it too. -/
def Outcome.state : Outcome Symbol Formula Output → State Symbol Formula
  | .done _ state | .failed _ state => state

/-- A force step either suspends the same cell or supplies its cached result. -/
inductive Event (Symbol Formula : Type) where
  | more (cursor : SourceCurrentConjunctionRequirementPull.Cursor Symbol Formula)
  | complete (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))

/-- Start with no private cells and the supplied actual physical state. -/
def initial (before : Physical Symbol Formula) : State Symbol Formula := ⟨[], before⟩

/-- Read the stable natural-number handle without executing its cell. -/
def lookup (handle : Nat) (before : State Symbol Formula) : Option (Cell Symbol Formula) :=
  before.cells[handle]?

/-- Append a cell and return its stable index. -/
def allocate (cell : Cell Symbol Formula) (before : State Symbol Formula) : Nat × State Symbol Formula :=
  (before.cells.length, {before with cells := before.cells ++ [cell]})

/-- Replace an existing cell without inserting or removing any handle. -/
def update (handle : Nat) (cell : Cell Symbol Formula) (before : State Symbol Formula) : State Symbol Formula :=
  {before with cells := before.cells.set handle cell}

/-- The allocated handle reads the exact appended cell. -/
theorem lookup_allocate (cell : Cell Symbol Formula) (before : State Symbol Formula) :
    lookup (allocate cell before).1 (allocate cell before).2 = some cell := by
  simp [lookup, allocate]

/-- Appending a new cell retains each existing handle and its value. -/
theorem lookup_allocate_old (cell : Cell Symbol Formula) (before : State Symbol Formula)
    (handle : Nat) (original : Cell Symbol Formula) (found : lookup handle before = some original) :
    lookup handle (allocate cell before).2 = some original := by
  cases before with
  | mk cells physical =>
      change cells[handle]? = some original at found
      change (cells ++ [cell])[handle]? = some original
      induction cells generalizing handle with
      | nil => cases handle <;> cases found
      | cons first rest ih =>
          cases handle with
          | zero => exact found
          | succ handle => exact ih handle found

/-- Updating a present handle stores the replacement at that same handle. -/
theorem lookup_update (handle : Nat) (original replacement : Cell Symbol Formula)
    (before : State Symbol Formula) (found : lookup handle before = some original) :
    lookup handle (update handle replacement before) = some replacement := by
  cases before with
  | mk cells physical =>
      change cells[handle]? = some original at found
      change (cells.set handle replacement)[handle]? = some replacement
      induction cells generalizing handle with
      | nil => cases handle <;> cases found
      | cons first rest ih =>
          cases handle with
          | zero => rfl
          | succ handle => exact ih handle found

/-- A cell update does not change the allocation counter. -/
theorem update_length (handle : Nat) (cell : Cell Symbol Formula) (before : State Symbol Formula) :
    (update handle cell before).cells.length = before.cells.length := by
  simp only [update, List.length_set]

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Execute at most one actual pending projection and update its own cell. -/
def forceStep (p h handle : Nat) (before : State Symbol Formula) :
    Outcome Symbol Formula (Event Symbol Formula) :=
  match lookup handle before with
  | none => .failed (.missing handle) before
  | some (.done nodes) => .done (.complete nodes) before
  | some (.column nodes) =>
      let result := SourceCurrentConjunctionRequirements.canonical nodes
      .done (.complete result) (update handle (.done result) before)
  | some (.pending cursor) =>
      match SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
      | .failed fault physical => .failed (.projection handle cursor fault) {before with physical := physical}
      | .done (.complete nodes) physical =>
          .done (.complete nodes) (update handle (.done nodes) {before with physical := physical})
      | .done (.more next) physical =>
          .done (.more next) (update handle (.pending next) {before with physical := physical})

/-- A completed-cell hit retains the identical complete state and executes no projection. -/
theorem forceStep_hit (p h handle : Nat) (nodes : List Node) (before : State Symbol Formula)
    (found : lookup handle before = some (.done nodes)) :
    forceStep p h handle before = .done (.complete nodes) before := by
  simp only [forceStep, found]

/-- Missing handles fail before any physical operation or cell update. -/
theorem forceStep_missing (p h handle : Nat) (before : State Symbol Formula)
    (absent : lookup handle before = none) :
    forceStep p h handle before = .failed (.missing handle) before := by
  simp only [forceStep, absent]

/-- A projection failure retains its original cell cursor and exact reached physical state. -/
theorem forceStep_failed (p h handle : Nat) (cursor : Cursor) (before : State Symbol Formula)
    (after : Physical Symbol Formula) (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (found : lookup handle before = some (.pending cursor))
    (actual : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical = .failed fault after) :
    forceStep p h handle before =
      .failed (.projection handle cursor fault) {before with physical := after} := by
  simp only [forceStep, found, actual]

/-- The selected pending cell supplies the finite job measure. -/
def remaining (handle : Nat) (before : State Symbol Formula) : Nat :=
  match lookup handle before with
  | some (.pending cursor) => cursor.pending.length
  | _ => 0

private theorem cursor_more_decreases (p h : Nat) (cursor next : Cursor)
    (before after : Physical Symbol Formula)
    (actual : SourceCurrentConjunctionRequirementPull.step p h cursor before = .done (.more next) after) :
    next.pending.length < cursor.pending.length := by
  cases cursor with
  | mk pending collected =>
      cases pending with
      | nil => simp only [SourceCurrentConjunctionRequirementPull.step] at actual; cases actual
      | cons job rest =>
          cases projected : SourceCurrentConjunctionRequirementPull.projection p h job before with
          | failed fault physical =>
              simp only [SourceCurrentConjunctionRequirementPull.step, projected,
                SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
              cases actual
          | done value physical =>
              simp only [SourceCurrentConjunctionRequirementPull.step, projected,
                SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
              split at actual
              · cases actual
              · cases actual
                exact Nat.lt_succ_self _

/-- An actual suspended step strictly reduces the selected cell's pending jobs. -/
theorem forceStep_more_decreases (p h handle : Nat) (before after : State Symbol Formula)
    (next : Cursor) (actual : forceStep p h handle before = .done (.more next) after) :
    remaining handle after < remaining handle before := by
  cases found : lookup handle before with
  | none => simp only [forceStep, found] at actual; cases actual
  | some cell =>
      cases cell with
      | column nodes => simp only [forceStep, found] at actual; cases actual
      | done nodes => simp only [forceStep, found] at actual; cases actual
      | pending cursor =>
          cases observed : SourceCurrentConjunctionRequirementPull.step p h cursor before.physical with
          | failed fault physical => simp only [forceStep, found, observed] at actual; cases actual
          | done event physical =>
              cases event with
              | complete nodes => simp only [forceStep, found, observed] at actual; cases actual
              | more current =>
                  simp only [forceStep, found, observed] at actual
                  have same : update handle (.pending current) {before with physical := physical} = after :=
                    congrArg Outcome.state actual
                  rw [← same]
                  have present : lookup handle {before with physical := physical} = some (.pending cursor) := found
                  simp only [remaining, lookup_update handle (.pending cursor) (.pending current) _ present, found]
                  exact cursor_more_decreases p h cursor current before.physical physical observed

/-- Force the finite pending cursor without an administrative execution bound. -/
def force (p h handle : Nat) (before : State Symbol Formula) : Outcome Symbol Formula (List Node) :=
  match _actual : forceStep p h handle before with
  | .failed fault after => .failed fault after
  | .done (.complete nodes) after => .done nodes after
  | .done (.more _) after => force p h handle after
termination_by remaining handle before
decreasing_by exact forceStep_more_decreases p h handle before _ _ _actual

/-- Complete forcing repeats the literal transition and retains its exact first failure. -/
theorem force_step (p h handle : Nat) (before : State Symbol Formula) :
    force p h handle before =
      match forceStep p h handle before with
      | .failed fault after => .failed fault after
      | .done (.complete nodes) after => .done nodes after
      | .done (.more _) after => force p h handle after := by
  rw [force.eq_def]
  cases forceStep p h handle before with
  | failed fault after => rfl
  | done event after => cases event <;> rfl

/-- Every completed-cell force retains the identical state and cached result. -/
theorem force_hit (p h handle : Nat) (nodes : List Node) (before : State Symbol Formula)
    (found : lookup handle before = some (.done nodes)) :
    force p h handle before = .done nodes before := by
  rw [force_step, forceStep_hit p h handle nodes before found]

end MicroCFTA.SourceCurrentConjunctionRequirementCells
