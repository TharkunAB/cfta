import MicroCFTA.SourceCurrentAllocatedLocalWorker

namespace MicroCFTA.CurrentLocalWorkerChecks
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

-- A prefix error needs no continuation budget or child availability and retains exact operation tables.
example (loaded : Allocated) (inherited : EqValue) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) (message : String)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .error message) :
    let returned := reduce 0 0 0 0 0 0 0 0 0 0 loaded inherited values before fourth memo
    returned = .failed (.precheck message) (prefixState before loaded inherited) fourth memo ∧
      returned.state.native = before.native ∧
      returned.state.operations = (runPrefix loaded.stored loaded.guard inherited before.operations).2 ∧
      returned.fourth = fourth ∧ returned.memo = memo := by
  dsimp only
  rw [reduce_error 0 0 0 0 0 0 0 0 0 0 loaded inherited values before fourth memo message actual]
  exact ⟨rfl, SourceCurrentAllocatedPrecheck.state_native before loaded inherited,
    SourceCurrentAllocatedPrecheck.state_operations before loaded inherited, rfl, rfl⟩

-- A contradictory branch preserves the source child-list length, including the empty list.
example (loaded : Allocated) (inherited : EqValue) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren) :
    reduce 0 0 0 0 0 0 0 0 0 0 loaded inherited values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before loaded inherited) fourth memo ∧
      (EqualityLeafProjectionRuntimeEmpty.erase values).length = values.length := by
  exact ⟨reduce_emptyChildren 0 0 0 0 0 0 0 0 0 0 loaded inherited values before fourth memo actual,
    by simp [EqualityLeafProjectionRuntimeEmpty.erase]⟩

-- A stopped Scan requires neither a requirement return nor a class-edit return.
example (g s r e p h m c n budget : Nat) (records selected : List Record)
    (values : List (Value Symbol Guard)) (before after : Checked width) (paths : Class)
    (fourth saved : Fourth) (memo : Memo)
    (actual : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
      .done (some paths, selected) after saved) :
    classes g s r e p h m c n budget records values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values) after saved memo := by
  simp only [classes, scan, actual, Outcome.bind]

-- Required failure keeps its exact observed heap, original operation state, fourth memo, and merge memo.
example (r h : Nat) (paths : List SourceEqualityNeeded.Path) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (key : InternedBinderProtocol.NodeKey) (heap : Heap)
    (actual : SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap = .pending key heap) :
    required r h paths values before fourth memo =
      .failed (.required (.pending key heap)) (advanceHeap before heap) fourth memo := by
  simp only [required, actual]

-- The full failed shared state remains inside the class diagnostic; its target slots are not discarded.
example (e p h m c n : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (fault : SourceCurrentAllocatedSharedEditWorker.Fault width)
    (shared : SourceCurrentAllocatedSharedTargetState.State width)
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo = .failed fault shared) :
    pass e p h m c n records values before fourth memo =
      .failed (.classes (.failed fault shared)) shared.checked fourth shared.memo := by
  simp only [pass, actual]

-- Live continuation uses selected original records and the literal required forest at its returned heap.
example (g s r e p h m c n budget : Nat) (records selected : List Record)
    (values requiredValues results : List (Value Symbol Guard))
    (before middle after : Checked width) (heap : Heap) (fourth savedFourth : Fourth) (memo saved : Memo)
    (scanned : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth =
      .done (none, selected) middle savedFourth)
    (required : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (selected.map SourceEqualityClassOrder.Record.paths))
      values middle.native.machine.heap = .done requiredValues heap)
    (edited : SourceCurrentAllocatedClassWorker.pass e p h m c n selected requiredValues
      (advanceHeap middle heap) memo = .done results after saved) :
    classes g s r e p h m c n budget records values before fourth memo =
      .done results after savedFourth saved := by
  simp only [classes, scan, scanned, Outcome.bind, SourceCurrentAllocatedLocalWorker.required,
    required, pass, edited]

end MicroCFTA.CurrentLocalWorkerChecks
