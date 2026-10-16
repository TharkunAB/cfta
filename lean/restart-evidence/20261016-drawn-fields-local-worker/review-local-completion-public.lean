import MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.required_complete
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.required_complete
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.classes_complete
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.classes_complete
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete

namespace MicroCFTA.LocalCompletionIndependentProbes
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker
open SourceCurrentAllocatedLocalWorkerCompletion
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- A stopped Scan needs zero structural, edit, merge, and comparison bounds.
example {budget : Nat} {records : List Record} {values : List (Value Symbol Guard)}
    {before after : Checked width} {fourth saved : Fourth} {memo : Memo} {paths : Class} {selected : Constraints}
    (actual : SourceCurrentConjunctionClassScan.Scan budget source reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth (some paths) selected after saved) :
    ∃ g s p h n, ∀ G S P H N, g ≤ G → s ≤ S → p ≤ P → h ≤ H → n ≤ N →
      classes G S 0 0 P H 0 0 N budget records values before fourth memo =
        .done (EqualityLeafProjectionRuntimeEmpty.erase values) after saved memo := by
  obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actual
  obtain ⟨g, s, p, h, n, done⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
  refine ⟨g, s, p, h, n, ?_⟩
  intro G S P H N enoughG enoughS enoughP enoughH enoughN
  have first := done G S P H N enoughG enoughS enoughP enoughH enoughN
  simp only [classes, scan, first, Outcome.bind]

-- The same selected original records flow through required reconstruction and class right fold.
example {budget : Nat} {records kept : List Record} {values requiredValues results : List (Value Symbol Guard)}
    {before middle after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {selected : Constraints} {heap : Heap} {r h : Nat}
    (actualScan : SourceCurrentConjunctionClassScan.Scan budget source reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth none selected middle savedFourth)
    (retained : Retained actualScan records kept)
    (actualRequired : SourceEqualityRequiredExecution.requireAll r h (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done requiredValues heap)
    (actualPass : SourceCurrentAllocatedClassPass.Pass kept requiredValues
      (SourceCurrentConjunctionClassScan.advanceHeap middle heap) memo results after saved) :
    kept.Sublist records ∧ kept.map SourceEqualityClassOrder.Record.paths = selected ∧
      StableRun (fun g s r e p h m c n => classes g s r e p h m c n budget records values before fourth memo)
        results after savedFourth saved :=
  ⟨retained.fields.1, retained.fields.2, classes_complete (.completed actualScan retained actualRequired actualPass)⟩

-- Every larger nine-bound execution starts from the same actual precheck return.
example {budget : Nat} {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
      results after savedFourth saved) :
    ∃ g s r e p h m c n,
      reduce g s r e p h m c n budget loaded inherited values before fourth memo =
        .done results after savedFourth saved := by
  obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ := reduce_complete actual
  exact ⟨g, s, r, e, p, h, m, c, n,
    stable g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩

-- An unchanged precheck returns with zero bounds and retains both warm result memos.
example (budget : Nat) (loaded : Allocated) (inherited : EqValue) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (actual : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok .unchanged) :
    reduce 0 0 0 0 0 0 0 0 0 budget loaded inherited values before fourth memo =
      .done values (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo :=
  reduce_unchanged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual

-- A contradictory precheck erases the original slots and skips every bounded continuation.
example (budget : Nat) (loaded : Allocated) (inherited : EqValue) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (actual : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok .emptyChildren) :
    reduce 0 0 0 0 0 0 0 0 0 budget loaded inherited values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values)
        (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo :=
  reduce_emptyChildren _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual
end MicroCFTA.LocalCompletionIndependentProbes
