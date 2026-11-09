import MicroCFTA.SourceCurrentConjunctionTuplePullTotal
import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.SourceCurrentConjunctionWorker

/-!
# Actual transitions for shared requirement work

The table and pending queue retain the same row-spine handle. A requirement
cell is forced before its Empty or budget test. Positive admission schedules
its descendants before the remaining parent requirements and row suffix.
Overflow retains the old suffix at budget zero. A fault retains the private
heaps and unforced queue. These transitions are not yet the selected caller.
Termination, terminal materialization, and whole-call contracts are separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
open InternedConstructorTemplates
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

/-- A table entry retains its query and shared row stream; zero sampling has no rows. -/
structure Entry (Symbol Formula : Type) where
  nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula))
  rows : Option Nat

/-- Pending tasks retain conjunctions, separate requirement cells, or a row stream. -/
inductive Task (Symbol Formula : Type) where
  | nodes (values : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
  | requirements (handles : List Nat)
  | rows (handle : Nat)

/-- One state retains the budget, table, literal task order, and both private heaps. -/
structure State (Symbol Formula : Type) where
  budget : Nat
  table : List (Entry Symbol Formula)
  pending : List (Task Symbol Formula)
  storage : SourceCurrentConjunctionRequirementRows.State Symbol Formula

/-- Faults distinguish raw sampling, requirement forcing, and row preparation. -/
inductive Fault (Symbol Formula : Type) where
  | sample (actual : SourceCurrentConjunctionRowsWorker.Fault)
  | requirement (actual : SourceCurrentConjunctionRequirementCells.Fault Symbol Formula)
  | rows (actual : SourceCurrentConjunctionRequirementRows.Fault)

/-- A drained queue still requires the terminal materialization proof. -/
inductive Event where
  | more
  | drained

/-- Every transition retains its entire actual private and physical state. -/
inductive Outcome (Symbol Formula : Type) where
  | done (event : Event) (state : State Symbol Formula)
  | failed (fault : Fault Symbol Formula) (state : State Symbol Formula)

/-- Both successful and failed transitions expose their exact reached state. -/
def Outcome.state : Outcome Symbol Formula → State Symbol Formula
  | .done _ state | .failed _ state => state

/-- Query-only skip tests do not read a stored row stream. -/
def queryTable (table : List (Entry Symbol Formula)) : SourceCurrentConjunctionWorker.Table Symbol Formula :=
  table.map fun entry => ⟨entry.nodes, []⟩

/-- Replace only the actual physical state after a native observation. -/
def withPhysical (before : State Symbol Formula) (physical : Physical) : State Symbol Formula :=
  {before with storage := {before.storage with requirements :=
    {before.storage.requirements with physical := physical}}}

/-- The query starts with no private cells or table entries. -/
def initial (budget : Nat) (start : Node) (before : Physical) : State Symbol Formula :=
  ⟨budget, [], [.nodes [start]], SourceCurrentConjunctionRequirementRows.initial before⟩

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Test a forced conjunction, then sample before any row equality or projection. -/
noncomputable def visit (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) : Outcome Symbol Formula :=
  if nodes.any isEmpty then .done .more {before with pending := rest}
  else if SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes then
    .done .more {before with pending := rest}
  else
    match SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes before.storage.requirements.physical with
    | .failed fault physical =>
        .failed (.sample fault) {(withPhysical before physical) with pending := .nodes nodes :: rest}
    | .done (.overflow _ _) physical =>
        .done .more {(withPhysical before physical) with budget := 0, pending := rest}
    | .done (.fit []) physical =>
        .done .more {(withPhysical before physical) with
          table := ⟨nodes, none⟩ :: before.table, pending := rest}
    | .done (.fit (tuple :: tuples)) physical =>
        let exposed := withPhysical before physical
        let allocated := SourceCurrentConjunctionRequirementRows.allocateSpine (.pending (tuple :: tuples)) exposed.storage
        .done .more {exposed with
          budget := before.budget - (tuples.length + 1)
          table := ⟨nodes, some allocated.1⟩ :: before.table
          pending := .rows allocated.1 :: rest
          storage := allocated.2}

/-- Advance the actual shared task at the head without forcing the unused suffix. -/
noncomputable def step (p h : Nat) (before : State Symbol Formula) : Outcome Symbol Formula :=
  match before.pending with
  | [] => .done .drained before
  | .nodes nodes :: rest => visit h nodes rest before
  | .requirements [] :: rest => .done .more {before with pending := rest}
  | .requirements (handle :: handles) :: rest =>
      match SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements with
      | .failed fault cells =>
          .failed (.requirement fault) {before with storage := {before.storage with requirements := cells}}
      | .done nodes cells =>
          visit h nodes (.requirements handles :: rest)
            {before with storage := {before.storage with requirements := cells}}
  | .rows handle :: rest =>
      match SourceCurrentConjunctionRequirementRows.nextRow handle before.storage with
      | .failed fault storage => .failed (.rows fault) {before with storage := storage}
      | .done none storage => .done .more {before with storage := storage, pending := rest}
      | .done (some (handles, tail)) storage =>
          .done .more {before with
            storage := storage
            pending := .requirements handles :: .rows tail :: rest}

/-- A drained queue performs no new native or private operation. -/
theorem step_nil (p h : Nat) (before : State Symbol Formula) (empty : before.pending = []) :
    step p h before = .done .drained before := by
  simp only [step, empty]

/-- A direct conjunction uses the same actual visit as a forced requirement. -/
theorem step_nodes (p h : Nat) (before : State Symbol Formula) (nodes : List Node)
    (rest : List (Task Symbol Formula)) (pending : before.pending = .nodes nodes :: rest) :
    step p h before = visit h nodes rest before := by
  simp only [step, pending]

/-- An empty requirement list removes no row suffix or later task. -/
theorem step_requirements_nil (p h : Nat) (before : State Symbol Formula)
    (rest : List (Task Symbol Formula)) (pending : before.pending = .requirements [] :: rest) :
    step p h before = .done .more {before with pending := rest} := by
  simp only [step, pending]

/-- A requirement failure retains its actual cells and the unforced task suffix. -/
theorem step_requirement_failed (p h handle : Nat) (handles : List Nat)
    (before : State Symbol Formula) (rest : List (Task Symbol Formula))
    (fault : SourceCurrentConjunctionRequirementCells.Fault Symbol Formula)
    (cells : SourceCurrentConjunctionRequirementCells.State Symbol Formula)
    (pending : before.pending = .requirements (handle :: handles) :: rest)
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements =
      .failed fault cells) :
    step p h before = .failed (.requirement fault)
      {before with storage := {before.storage with requirements := cells}} := by
  simp only [step, pending, actual]

/-- A forced requirement is tested before any following requirement or row stream. -/
theorem step_requirement_done (p h handle : Nat) (handles : List Nat)
    (before : State Symbol Formula) (rest : List (Task Symbol Formula)) (nodes : List Node)
    (cells : SourceCurrentConjunctionRequirementCells.State Symbol Formula)
    (pending : before.pending = .requirements (handle :: handles) :: rest)
    (actual : SourceCurrentConjunctionRequirementCells.force p h handle before.storage.requirements =
      .done nodes cells) :
    step p h before = visit h nodes (.requirements handles :: rest)
      {before with storage := {before.storage with requirements := cells}} := by
  simp only [step, pending, actual]

/-- A row failure retains the actual private heaps and all remaining work. -/
theorem step_rows_failed (p h handle : Nat) (before : State Symbol Formula)
    (rest : List (Task Symbol Formula)) (fault : SourceCurrentConjunctionRequirementRows.Fault)
    (storage : Storage) (pending : before.pending = .rows handle :: rest)
    (actual : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .failed fault storage) :
    step p h before = .failed (.rows fault) {before with storage := storage} := by
  simp only [step, pending, actual]

/-- A completed row stream removes only that stream task. -/
theorem step_rows_none (p h handle : Nat) (before : State Symbol Formula)
    (rest : List (Task Symbol Formula)) (storage : Storage)
    (pending : before.pending = .rows handle :: rest)
    (actual : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage = .done none storage) :
    step p h before = .done .more {before with storage := storage, pending := rest} := by
  simp only [step, pending, actual]

/-- A live row schedules each requirement before the shared cached tail and old suffix. -/
theorem step_rows_live (p h handle tail : Nat) (before : State Symbol Formula)
    (rest : List (Task Symbol Formula)) (handles : List Nat) (storage : Storage)
    (pending : before.pending = .rows handle :: rest)
    (actual : SourceCurrentConjunctionRequirementRows.nextRow handle before.storage =
      .done (some (handles, tail)) storage) :
    step p h before = .done .more {before with
      storage := storage
      pending := .requirements handles :: .rows tail :: rest} := by
  simp only [step, pending, actual]

/-- Empty removes only this forced conjunction before any budget or sampling test. -/
theorem visit_empty (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (empty : nodes.any isEmpty = true) :
    visit h nodes rest before = .done .more {before with pending := rest} := by
  simp only [visit, empty, ite_true]

/-- Budget, open, and repeated-query skips do not force any row stream. -/
theorem visit_skip (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (nonempty : nodes.any isEmpty = false)
    (skipped : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes = true) :
    visit h nodes rest before = .done .more {before with pending := rest} := by
  simp only [visit, nonempty, Bool.false_eq_true, ite_false, skipped, ite_true]

/-- A sampling fault retains the forced query and exact reached physical state. -/
theorem visit_failed (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (physical : Physical) (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes = false)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
      before.storage.requirements.physical = .failed fault physical) :
    visit h nodes rest before = .failed (.sample fault)
      {(withPhysical before physical) with pending := .nodes nodes :: rest} := by
  simp only [visit, nonempty, fresh, Bool.false_eq_true, ite_false, actual]

/-- Overflow schedules the complete old suffix at zero budget without a table insertion. -/
theorem visit_overflow (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (physical : Physical)
    (tuples : List (List (EdgeValue Symbol Guard)))
    (cursor : SourceCurrentConjunctionTuplePull.Cursor Symbol Formula)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes = false)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
      before.storage.requirements.physical = .done (.overflow tuples cursor) physical) :
    visit h nodes rest before = .done .more
      {(withPhysical before physical) with budget := 0, pending := rest} := by
  simp only [visit, nonempty, fresh, Bool.false_eq_true, ite_false, actual]

/-- A zero sample stores an empty row stream and retains the remaining budget. -/
theorem visit_zero (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (physical : Physical)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes = false)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
      before.storage.requirements.physical = .done (.fit []) physical) :
    visit h nodes rest before = .done .more {(withPhysical before physical) with
      table := ⟨nodes, none⟩ :: before.table, pending := rest} := by
  simp only [visit, nonempty, fresh, Bool.false_eq_true, ite_false, actual]

/-- Positive admission shares one raw-row handle between the table and the queue. -/
theorem visit_positive (h : Nat) (nodes : List Node) (rest : List (Task Symbol Formula))
    (before : State Symbol Formula) (physical : Physical)
    (tuple : List (EdgeValue Symbol Guard)) (tuples : List (List (EdgeValue Symbol Guard)))
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key SourceCurrentConjunctionWorklist.closed
      before.budget (queryTable before.table) nodes = false)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
      before.storage.requirements.physical = .done (.fit (tuple :: tuples)) physical) :
    let exposed := withPhysical before physical
    let allocated := SourceCurrentConjunctionRequirementRows.allocateSpine (.pending (tuple :: tuples)) exposed.storage
    visit h nodes rest before = .done .more {exposed with
      budget := before.budget - (tuples.length + 1)
      table := ⟨nodes, some allocated.1⟩ :: before.table
      pending := .rows allocated.1 :: rest
      storage := allocated.2} := by
  simp only [visit, nonempty, fresh, Bool.false_eq_true, ite_false, actual]

end MicroCFTA.SourceCurrentConjunctionSharedWorklistStep
