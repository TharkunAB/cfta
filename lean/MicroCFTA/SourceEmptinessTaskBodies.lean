import MicroCFTA.SourceEmptinessTaskTrace

/-!
# Original captured bodies through reached task effects

A body receipt records the original forest and path order at a handle.
The receipt permits a suspended or completed result. Actual task effects
retain each existing body, including the body of a cell that they fill.
Row receipts retain direct children before the ordered class handles.
These proofs use complete row reads and the existing scoped native state.
They do not establish the Haskell lazy row schedule or a checked-state transfer.
-/
namespace MicroCFTA.SourceEmptinessTaskBodies
open Language EqualityNormalize InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEmptinessTasks SourceEmptinessTaskRows
local notation "TaskState" => SourceEmptinessTasks.State

/-- A handle retains its exact original body, with either result status. -/
def BodyReceipt (state : TaskState width Symbol Guard) (body : Body Symbol Guard)
    (task : Task Symbol Guard) : Prop :=
  ∃ handle cell, task = .captured handle ∧ state.cells handle = some cell ∧ cell.body = body

/-- Every existing handle keeps its original body. Its result may become complete. -/
def RetainsBodies (before after : TaskState width Symbol Guard) : Prop :=
  ∀ handle cell, before.cells handle = some cell →
    ∃ later, after.cells handle = some later ∧ later.body = cell.body

/-- An unchanged task store retains every body. -/
theorem RetainsBodies.refl (state : TaskState width Symbol Guard) : RetainsBodies state state :=
  fun _ cell found => ⟨cell, found, rfl⟩

/-- Consecutive task effects retain the same original bodies. -/
theorem RetainsBodies.trans {before middle after : TaskState width Symbol Guard}
    (first : RetainsBodies before middle) (second : RetainsBodies middle after) : RetainsBodies before after := by
  intro handle cell found
  obtain ⟨intermediate, present, same⟩ := first handle cell found
  obtain ⟨later, final, equal⟩ := second handle intermediate present
  exact ⟨later, final, equal.trans same⟩

/-- Body retention transports a receipt even when the cell becomes complete. -/
theorem BodyReceipt.transport {before after : TaskState width Symbol Guard}
    {body : Body Symbol Guard} {task : Task Symbol Guard}
    (receipt : BodyReceipt before body task) (retained : RetainsBodies before after) :
    BodyReceipt after body task := by
  obtain ⟨handle, cell, taskEq, found, bodyEq⟩ := receipt
  obtain ⟨later, present, same⟩ := retained handle cell found
  exact ⟨handle, later, taskEq, present, same.trans bodyEq⟩

/-- Freshness places every existing cell below the next task handle. -/
theorem issued_of_found [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {state : TaskState width Symbol Guard}
    (ready : Ready emptyGuard conjoin state) {handle : Nat} {cell : Cell Symbol Guard}
    (found : state.cells handle = some cell) : handle < state.next := by
  by_cases earlier : handle < state.next
  · exact earlier
  · have absent := ready.fresh handle (by omega)
    rw [found] at absent
    cases absent

/-- Fresh capture retains every original body in the existing task store. -/
theorem capture_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (body : Body Symbol Guard)
    (state : TaskState width Symbol Guard) (ready : Ready emptyGuard conjoin state) :
    RetainsBodies state (capture body state).2 := by
  intro handle cell found
  have different : handle ≠ state.next := by have earlier := issued_of_found ready found; omega
  exact ⟨cell, by simpa only [capture, different, ↓reduceIte] using found, rfl⟩

/-- A new capture supplies its original body at the returned handle. -/
theorem capture_body (body : Body Symbol Guard) (state : TaskState width Symbol Guard) :
    BodyReceipt (capture body state).2 body (capture body state).1 :=
  ⟨state.next, ⟨body, none⟩, rfl, by simp only [capture, ↓reduceIte], rfl⟩

/-- First completion changes the result but retains the body's original fields. -/
theorem finish_bodies (before : TaskState width Symbol Guard) (handle : Nat) (cell : Cell Symbol Guard)
    (value : Value Symbol Guard) (native : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (found : before.cells handle = some cell) : RetainsBodies before (finish before handle cell value native) := by
  intro current stored present
  by_cases same : current = handle
  · subst current
    have equal : stored = cell := Option.some.inj (present.symm.trans found)
    subst stored
    exact ⟨{cell with result := some value}, by simp only [finish, ↓reduceIte], rfl⟩
  · exact ⟨stored, by simpa only [finish, same, ↓reduceIte] using present, rfl⟩

/-- A native-state advance leaves every captured body unchanged. -/
theorem advanceNative_bodies (before : TaskState width Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    RetainsBodies before (advanceNative before native) := fun _ cell found => ⟨cell, found, rfl⟩

/-- Each actual force retains every existing body, including its own completed cell. -/
theorem force_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {task : Task Symbol Guard} {before after : TaskState width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin task before value after) : RetainsBodies before after := by
  cases trace with
  | value => exact .refl _
  | hit => exact .refl _
  | miss found _ _ => exact finish_bodies _ _ _ _ _ found

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Row" => ConservativeEmptinessRows.Row (Value Symbol Guard)

/-- Ordered class capture retains every previously issued body. -/
theorem captureClasses_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (children : List (Value Symbol Guard)) (classes : Constraints) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state) : RetainsBodies state (captureClasses children classes state).2 := by
  intro handle cell found
  exact ⟨cell, (captureClasses_earlier children classes state handle (issued_of_found ready found)).trans found, rfl⟩

/-- Capturing a row retains every body that existed before the row. -/
theorem captureRow_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (row : Row) (state : TaskState width Symbol Guard) (ready : Ready emptyGuard conjoin state) :
    RetainsBodies state (captureRow row state).2 := captureClasses_bodies row.children row.classes state ready

/-- Capturing all rows retains every body that existed before exposure. -/
theorem captureRows_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (rows : List Row) (state : TaskState width Symbol Guard) (ready : Ready emptyGuard conjoin state) :
    RetainsBodies state (captureRows rows state).2 := by
  intro handle cell found
  exact ⟨cell, (captureRows_earlier rows state handle (issued_of_found ready found)).trans found, rfl⟩

/-- An actual complete row read and its captures retain all earlier bodies. -/
theorem expose_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : TaskState width Symbol Guard} {rows : List (List (Task Symbol Guard))}
    (trace : Expose value before rows after) (ready : Ready emptyGuard conjoin before) : RetainsBodies before after := by
  cases trace with
  | read _available _closed _actual =>
      rename_i edges readHeap
      intro handle cell found
      have captured := captureRows_earlier (SourceEmptinessExposure.rows edges)
        (advanceNative before (SourceEqualityNativeScoped.advanceHeap before.native readHeap)) handle
        (issued_of_found ready found)
      exact ⟨cell, captured.trans found, rfl⟩

/-- Reached worklist execution retains every initially captured body. -/
theorem run_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending before final after) :
    Ready emptyGuard conjoin before → RetainsBodies before after := by
  induction trace with
  | done => intro _; exact .refl _
  | empty forced _ _ ih =>
      intro ready
      exact (force_bodies forced).trans (ih (forced.effects ready).1)
  | skipped forced _ _ _ ih =>
      intro ready
      exact (force_bodies forced).trans (ih (forced.effects ready).1)
  | admit forced _ _ exposed _ ih =>
      intro ready
      have first := forced.effects ready
      exact (force_bodies forced).trans ((expose_bodies exposed first.1).trans (ih (exposed.effects first.1).1))

/-- A class handle retains its original forest and class paths after completion. -/
def ClassBodyReceipt (children : List (Value Symbol Guard)) (state : TaskState width Symbol Guard)
    (paths : Class) (task : Task Symbol Guard) : Prop := BodyReceipt state (classBody children paths) task

/-- A body-only row receipt keeps the direct child prefix and original class order. -/
def RowBodyReceipt (state : TaskState width Symbol Guard) (row : Row) (tasks : List (Task Symbol Guard)) : Prop :=
  ∃ classes, tasks = row.children.map Task.value ++ classes ∧
    All₂ (ClassBodyReceipt row.children state) row.classes classes

/-- An exact suspended class receipt supplies its body-only receipt. -/
theorem classReceipt_body {children : List (Value Symbol Guard)} {state : TaskState width Symbol Guard}
    {paths : Class} {task : Task Symbol Guard} (receipt : ClassReceipt children state paths task) :
    ClassBodyReceipt children state paths task := by
  obtain ⟨handle, same, found⟩ := receipt
  exact ⟨handle, ⟨classBody children paths, none⟩, same, found, rfl⟩

/-- An exact suspended row receipt supplies the same child prefix and ordered bodies. -/
theorem rowReceipt_body {state : TaskState width Symbol Guard} {row : Row} {tasks : List (Task Symbol Guard)}
    (receipt : RowReceipt state row tasks) : RowBodyReceipt state row tasks := by
  obtain ⟨classes, same, receipts⟩ := receipt
  exact ⟨classes, same, receipts.imp (fun _ _ receipt => classReceipt_body receipt)⟩

/-- Body retention transports a class receipt without constraining its result status. -/
theorem ClassBodyReceipt.transport {before after : TaskState width Symbol Guard}
    {children : List (Value Symbol Guard)} {paths : Class} {task : Task Symbol Guard}
    (receipt : ClassBodyReceipt children before paths task) (retained : RetainsBodies before after) :
    ClassBodyReceipt children after paths task := BodyReceipt.transport receipt retained

/-- Body retention transports a row while keeping its exact child prefix and class order. -/
theorem RowBodyReceipt.transport {before after : TaskState width Symbol Guard}
    {row : Row} {tasks : List (Task Symbol Guard)} (receipt : RowBodyReceipt before row tasks)
    (retained : RetainsBodies before after) : RowBodyReceipt after row tasks := by
  obtain ⟨classes, same, receipts⟩ := receipt
  exact ⟨classes, same, receipts.imp (fun _ _ receipt => receipt.transport retained)⟩

/-- Actual class capture derives body receipts for all returned handles in order. -/
theorem captureClasses_receipt_body (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) :
    All₂ (ClassBodyReceipt children (captureClasses children classes state).2) classes
      (captureClasses children classes state).1 :=
  (captureClasses_receipt children classes state).imp (fun _ _ receipt => classReceipt_body receipt)

/-- Actual row capture derives the exact child prefix and class body receipts. -/
theorem captureRow_receipt_body (row : Row) (state : TaskState width Symbol Guard) :
    RowBodyReceipt (captureRow row state).2 row (captureRow row state).1 :=
  ⟨_, rfl, captureClasses_receipt_body row.children row.classes state⟩

/-- Actual multi-row capture derives ordered body receipts in its final returned store. -/
theorem captureRows_receipt_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (rows : List Row) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state)
    (inputs : ∀ row ∈ rows, Values state.native.machine.heap row.children ∧ ClosedValues row.children) :
    All₂ (RowBodyReceipt (captureRows rows state).2) rows (captureRows rows state).1 :=
  (captureRows_receipt rows state ready inputs).imp (fun _ _ receipt => rowReceipt_body receipt)

/-- Actual exposure supplies its original read and ordered body receipts at the reached store. -/
theorem expose_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : TaskState width Symbol Guard} {tasks : List (List (Task Symbol Guard))}
    (trace : Expose value before tasks after) (ready : Ready emptyGuard conjoin before) :
    ∃ edges readHeap, SourceEqualityProjectionRead.Read value before.native.machine.heap edges readHeap ∧
      InternedProbeProvenance.Available before.native.machine.heap value ∧ value.free = [] ∧
      All₂ (RowBodyReceipt after) (SourceEmptinessExposure.rows edges) tasks := by
  cases trace with
  | read available closed actual =>
      rename_i edges readHeap
      have checked := actual.verified ready.native.semantic available closed
      have advanced := ready.advanceNative (SourceEqualityNativeScoped.advanceHeap before.native readHeap)
        (ready.native.advance readHeap checked.1 checked.2.1) checked.1
      exact ⟨edges, readHeap, actual, available, closed, captureRows_receipt_body _ _ advanced
        (rows_inputs readHeap checked.2.1 edges checked.2.2.1 checked.2.2.2)⟩

/-- A captured body receipt remains valid at the final state of an actual reached run. -/
theorem run_body_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending before final after)
    (ready : Ready emptyGuard conjoin before) {body : Body Symbol Guard} {task : Task Symbol Guard}
    (receipt : BodyReceipt before body task) : BodyReceipt after body task :=
  receipt.transport (run_bodies trace ready)

/-- Actual execution transports the exact direct-child prefix and original class bodies. -/
theorem run_row_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending before final after)
    (ready : Ready emptyGuard conjoin before) {row : Row} {tasks : List (Task Symbol Guard)}
    (receipt : RowBodyReceipt before row tasks) : RowBodyReceipt after row tasks :=
  receipt.transport (run_bodies trace ready)

/-- Source exposure and a reached continuation derive original row bodies in the final store. -/
theorem expose_run_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before middle after : TaskState width Symbol Guard}
    {tasks : List (List (Task Symbol Guard))}
    (exposed : Expose value before tasks middle)
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard conjoin budget seen pending middle final after)
    (ready : Ready emptyGuard conjoin before) :
    ∃ edges readHeap, SourceEqualityProjectionRead.Read value before.native.machine.heap edges readHeap ∧
      InternedProbeProvenance.Available before.native.machine.heap value ∧ value.free = [] ∧
      All₂ (RowBodyReceipt after) (SourceEmptinessExposure.rows edges) tasks := by
  obtain ⟨edges, readHeap, actual, available, closed, receipts⟩ := expose_receipt exposed ready
  have retained := run_bodies trace (exposed.effects ready).1
  exact ⟨edges, readHeap, actual, available, closed,
    receipts.imp (fun _ _ receipt => receipt.transport retained)⟩

end MicroCFTA.SourceEmptinessTaskBodies
