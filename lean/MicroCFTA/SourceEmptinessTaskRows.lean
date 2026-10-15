import MicroCFTA.SourceEmptinessTasks
import MicroCFTA.SourceEmptinessExposure

/-!
# Ordered delayed requirements of actual source rows

Each row keeps its direct children first. Capture then stores one suspended
class body for each original class, in stored path order. Capture changes
only task storage. Exposure first completes the actual nodeEdges read and
retains its returned constructor heap. No class task is forced here.
-/
namespace MicroCFTA.SourceEmptinessTaskRows
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessTasks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Row" => ConservativeEmptinessRows.Row (Value Symbol Guard)
local notation "Tasks" => List (Task Symbol Guard)
local notation "TaskState" => SourceEmptinessTasks.State

/-- A suspended class retains the original forest and the original natural path order. -/
def classBody (children : List (Value Symbol Guard)) (paths : Class) : Body Symbol Guard :=
  ⟨children, paths.map (List.map Int.ofNat)⟩

/-- Capture the classes in source order without running their native folds. -/
def captureClasses (children : List (Value Symbol Guard)) : Constraints → TaskState width Symbol Guard →
    Tasks × TaskState width Symbol Guard
  | [], state => ([], state)
  | paths :: rest, state =>
      let first := capture (classBody children paths) state
      let later := captureClasses children rest first.2
      (first.1 :: later.1, later.2)

/-- Class capture leaves the complete native state unchanged. -/
theorem captureClasses_native (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) : (captureClasses children classes state).2.native = state.native := by
  induction classes generalizing state with
  | nil => rfl
  | cons paths rest ih => exact ih _

/-- Each class receives one fresh handle in the original class order. -/
theorem captureClasses_length (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) : (captureClasses children classes state).1.length = classes.length := by
  induction classes generalizing state with
  | nil => rfl
  | cons paths rest ih => simpa only [captureClasses, List.length_cons] using congrArg Nat.succ (ih _)

/-- Class capture issues exactly one fresh sidecar handle per original class. -/
theorem captureClasses_next (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) :
    (captureClasses children classes state).2.next = state.next + classes.length := by
  induction classes generalizing state with
  | nil => rfl
  | cons paths rest ih =>
      simpa only [captureClasses, capture, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (capture (classBody children paths) state).2

/-- Capture does not change a cell whose handle was already issued. -/
theorem captureClasses_earlier (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) (handle : Nat) (earlier : handle < state.next) :
    (captureClasses children classes state).2.cells handle = state.cells handle := by
  induction classes generalizing state with
  | nil => rfl
  | cons paths rest ih =>
      change (captureClasses children rest (capture (classBody children paths) state).2).2.cells handle = _
      rw [ih _ (by change handle < state.next + 1; omega)]
      have different : handle ≠ state.next := by omega
      simp only [capture, different, ↓reduceIte]

/-- An ordered class receipt retains the exact suspended body and its complete original forest. -/
def ClassReceipt (children : List (Value Symbol Guard)) (state : TaskState width Symbol Guard)
    (paths : Class) (task : Task Symbol Guard) : Prop :=
  ∃ handle, task = .captured handle ∧ state.cells handle = some ⟨classBody children paths, none⟩

/-- Every returned class handle points to its exact original body and remains suspended. -/
theorem captureClasses_receipt (children : List (Value Symbol Guard)) (classes : Constraints)
    (state : TaskState width Symbol Guard) :
    All₂ (ClassReceipt children (captureClasses children classes state).2) classes
      (captureClasses children classes state).1 := by
  induction classes generalizing state with
  | nil => exact .nil
  | cons paths rest ih =>
      apply All₂.cons
      · refine ⟨state.next, rfl, ?_⟩
        change (captureClasses children rest (capture (classBody children paths) state).2).2.cells state.next = _
        rw [captureClasses_earlier children rest _ state.next (by change state.next < state.next + 1; omega)]
        simp only [capture, ↓reduceIte]
      · exact ih _

/-- Closed available original forests derive readiness and retention through all captures. -/
theorem captureClasses_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (children : List (Value Symbol Guard)) (classes : Constraints) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state) (available : Values state.native.machine.heap children)
    (closed : ClosedValues children) :
    Ready emptyGuard conjoin (captureClasses children classes state).2 ∧
      Retains state (captureClasses children classes state).2 := by
  induction classes generalizing state with
  | nil => exact ⟨ready, .refl _⟩
  | cons paths rest ih =>
      have firstReady := capture_ready (classBody children paths) state ready available closed
      have later := ih _ firstReady available
      exact ⟨later.1, (capture_retains (classBody children paths) state ready).trans later.2⟩

/-- A row lists direct child values before its captured class handles. -/
def captureRow (row : Row) (state : TaskState width Symbol Guard) : Tasks × TaskState width Symbol Guard :=
  let classes := captureClasses row.children row.classes state
  (row.children.map Task.value ++ classes.1, classes.2)

/-- Row capture leaves the complete native state unchanged. -/
theorem captureRow_native (row : Row) (state : TaskState width Symbol Guard) :
    (captureRow row state).2.native = state.native := captureClasses_native row.children row.classes state

/-- Row capture derives readiness and preserves every previously completed task. -/
theorem captureRow_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (row : Row) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state) (available : Values state.native.machine.heap row.children)
    (closed : ClosedValues row.children) :
    Ready emptyGuard conjoin (captureRow row state).2 ∧ Retains state (captureRow row state).2 :=
  captureClasses_effects row.children row.classes state ready available closed

/-- Capture actual retained rows in their original source order. -/
def captureRows : List Row → TaskState width Symbol Guard → List Tasks × TaskState width Symbol Guard
  | [], state => ([], state)
  | row :: rest, state =>
      let first := captureRow row state
      let later := captureRows rest first.2
      (first.1 :: later.1, later.2)

/-- Capturing all source rows changes no native constructor, domain, or memo state. -/
theorem captureRows_native (rows : List Row) (state : TaskState width Symbol Guard) :
    (captureRows rows state).2.native = state.native := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih => exact (ih _).trans (captureRow_native row state)

/-- Source row order and multiplicity are retained exactly. -/
theorem captureRows_length (rows : List Row) (state : TaskState width Symbol Guard) :
    (captureRows rows state).1.length = rows.length := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih => simpa only [captureRows, List.length_cons] using congrArg Nat.succ (ih _)

/-- Later row captures retain all earlier issued cells, including suspended class bodies. -/
theorem captureRows_earlier (rows : List Row) (state : TaskState width Symbol Guard)
    (handle : Nat) (earlier : handle < state.next) :
    (captureRows rows state).2.cells handle = state.cells handle := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      change (captureRows rest (captureRow row state).2).2.cells handle = _
      rw [ih _ (by change handle < (captureClasses row.children row.classes state).2.next
                   rw [captureClasses_next]; omega)]
      exact captureClasses_earlier row.children row.classes state handle earlier

/-- Closed available row forests derive readiness and stable completed task results. -/
theorem captureRows_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (rows : List Row) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state)
    (inputs : ∀ row ∈ rows, Values state.native.machine.heap row.children ∧ ClosedValues row.children) :
    Ready emptyGuard conjoin (captureRows rows state).2 ∧ Retains state (captureRows rows state).2 := by
  induction rows generalizing state with
  | nil => exact ⟨ready, .refl _⟩
  | cons row rest ih =>
      have first := captureRow_effects row state ready (inputs row (by simp)).1 (inputs row (by simp)).2
      have later := ih _ first.1 (by
        intro other member
        simpa only [captureRow_native] using inputs other (List.mem_cons_of_mem row member))
      exact ⟨later.1, first.2.trans later.2⟩

/-- A complete captured row retains its child prefix and all exact suspended class bodies. -/
def RowReceipt (state : TaskState width Symbol Guard) (row : Row) (tasks : Tasks) : Prop :=
  ∃ classes, tasks = row.children.map Task.value ++ classes ∧
    All₂ (ClassReceipt row.children state) row.classes classes

/-- Every actual row has its exact child prefix and ordered class bodies in the final capture state. -/
theorem captureRows_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} (rows : List Row) (state : TaskState width Symbol Guard)
    (ready : Ready emptyGuard conjoin state)
    (inputs : ∀ row ∈ rows, Values state.native.machine.heap row.children ∧ ClosedValues row.children) :
    All₂ (RowReceipt (captureRows rows state).2) rows (captureRows rows state).1 := by
  induction rows generalizing state with
  | nil => exact .nil
  | cons row rest ih =>
      have first := captureRow_effects row state ready (inputs row (by simp)).1 (inputs row (by simp)).2
      apply All₂.cons
      · refine ⟨(captureClasses row.children row.classes state).1, rfl, ?_⟩
        apply (captureClasses_receipt row.children row.classes state).imp
        intro paths task receipt
        obtain ⟨handle, same, stored⟩ := receipt
        have earlier : handle < (captureRow row state).2.next := by
          by_cases earlier : handle < (captureRow row state).2.next
          · exact earlier
          · have absent := first.1.fresh handle (by omega)
            change (captureClasses row.children row.classes state).2.cells handle = none at absent
            rw [stored] at absent
            cases absent
        exact ⟨handle, same, (captureRows_earlier rest (captureRow row state).2 handle earlier).trans stored⟩
      · exact ih _ first.1 (by
          intro other member
          simpa only [captureRow_native] using inputs other (List.mem_cons_of_mem row member))

/-- Actual retained nodeEdges rows have closed available original child forests. -/
theorem rows_inputs (heap : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges heap edges) (closed : ClosedEdges edges) :
    ∀ row ∈ SourceEmptinessExposure.rows edges, Values heap row.children ∧ ClosedValues row.children := by
  intro row member
  obtain ⟨edge, selected, same⟩ := List.mem_map.mp member
  have original := (List.mem_filter.mp selected).1
  subst row
  exact ⟨semantic.ready.semantic.1.normal.facts.cached.edges _ edge (resident edge original), closed edge original⟩

/-- Exposure reads actual source edges, retains the returned native heap, and captures delayed rows. -/
inductive Expose [DecidableEq (EdgeKey Symbol Guard)] :
    Value Symbol Guard → TaskState width Symbol Guard → List Tasks → TaskState width Symbol Guard → Prop where
  | read (available : Available before.native.machine.heap value) (closed : value.free = [])
      (actual : SourceEqualityProjectionRead.Read value before.native.machine.heap edges heap) :
      Expose value before
        (captureRows (SourceEmptinessExposure.rows edges) (advanceNative before (advanceHeap before.native heap))).1
        (captureRows (SourceEmptinessExposure.rows edges) (advanceNative before (advanceHeap before.native heap))).2

/-- Actual exposure derives readiness and effects without forcing any captured class. -/
theorem Expose.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : TaskState width Symbol Guard} {rows : List Tasks}
    (trace : Expose value before rows after) (ready : Ready emptyGuard conjoin before) :
    Ready emptyGuard conjoin after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧ Retains before after := by
  cases trace with
  | read available closed actual =>
      rename_i edges heap
      have checked := actual.verified ready.native.semantic available closed
      have advanced := ready.advanceNative (advanceHeap before.native heap)
        (ready.native.advance heap checked.1 checked.2.1) checked.1
      have captured := captureRows_effects (SourceEmptinessExposure.rows edges) _ advanced
        (rows_inputs heap checked.2.1 edges checked.2.2.1 checked.2.2.2)
      refine ⟨captured.1, ?_, (advanceNative_retains before _).trans captured.2⟩
      rw [captureRows_native]
      exact checked.1

/-- Every closed available input has finite actual edge exposure and deterministic row capture. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (value : Value Symbol Guard) (before : TaskState width Symbol Guard) (ready : Ready emptyGuard conjoin before)
    (available : Available before.native.machine.heap value) (closed : value.free = []) :
    ∃ rows after, Expose value before rows after ∧ Ready emptyGuard conjoin after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Retains before after := by
  obtain ⟨edges, heap, read, _⟩ := SourceEqualityProjectionRead.complete value before.native.machine.heap
    ready.native.semantic available closed
  let trace : Expose value before
      (captureRows (SourceEmptinessExposure.rows edges) (advanceNative before (advanceHeap before.native heap))).1
      (captureRows (SourceEmptinessExposure.rows edges) (advanceNative before (advanceHeap before.native heap))).2 :=
    .read available closed read
  exact ⟨_, _, trace, trace.effects ready⟩

end MicroCFTA.SourceEmptinessTaskRows
