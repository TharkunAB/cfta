import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.select
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.select
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths_bind
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths_bind
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths_select
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.mapPaths_select
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan_nil
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan_nil
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan_mapPaths
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorker.scan_mapPaths
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.select_done_iff
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.select_done_iff
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.scan_done_stable
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.scan_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique
#check MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique

namespace MicroCFTA.RecordScanIndependentProbes
open Language EqualityNormalize InternedConstructorTemplates SourceEqualityClassOrder
open SourceCurrentAllocatedRecordScanWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Empty input retains the full checked state and fourth memo even at zero bounds.
example (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    scan 0 0 0 0 0 0 values [] before memo = .done (none, []) before memo := rfl

-- The selected failure prefix retains the literal reached state and memo.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (record : Record) (records : List Record) (before middle after : Checked width) (memo current saved : Memo)
    (head : SourceCurrentAllocatedScanWorker.gate true g values record.paths before memo = .done false middle current)
    (tail : scan g s p h n budget values records middle current = .failed fault after saved) :
    scan g s p h n budget values (record :: records) before memo =
      .failed (.selected record.paths fault) after saved := by
  simp only [scan, head, SourceCurrentAllocatedScanWorker.Outcome.bind,
    Bool.false_eq_true, ite_false, tail, select]

-- Equal paths with distinct tries retain both original occurrences in source order.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (first second : Record) (before middle after : Checked width) (memo current saved : Memo)
    (same : first.paths = second.paths) (different : first.trie ≠ second.trie)
    (one : SourceCurrentAllocatedScanWorker.gate true g values first.paths before memo = .done false middle current)
    (two : SourceCurrentAllocatedScanWorker.gate true g values second.paths middle current = .done false after saved) :
    scan g s p h n budget values [first, second] before memo = .done (none, [first, second]) after saved ∧
      first.paths = second.paths ∧ first.trie ≠ second.trie := by
  refine ⟨?_, same, different⟩
  simp only [scan, one, two, SourceCurrentAllocatedScanWorker.Outcome.bind,
    Bool.false_eq_true, ite_false, select]

-- A secondary skip executes its suffix at the exact secondary return.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (record : Record) (records : List Record) (before middle later after : Checked width)
    (memo current fourth saved : Memo) (result : Result)
    (primary : SourceCurrentAllocatedScanWorker.gate true g values record.paths before memo = .done true middle current)
    (secondary : SourceCurrentAllocatedScanWorker.gate false s values record.paths middle current = .done true later fourth)
    (tail : scan g s p h n budget values records later fourth = .done result after saved) :
    scan g s p h n budget values (record :: records) before memo = .done result after saved := by
  simp only [scan, primary, secondary, SourceCurrentAllocatedScanWorker.Outcome.bind, ite_true, tail]

-- A true decision returns before the suffix and retains the actual stopped paths.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (record : Record) (records : List Record) (value : Value Symbol Guard)
    (before middle later queried after : Checked width) (memo current fourth queryMemo saved : Memo)
    (primary : SourceCurrentAllocatedScanWorker.gate true g values record.paths before memo = .done true middle current)
    (secondary : SourceCurrentAllocatedScanWorker.gate false s values record.paths middle current = .done false later fourth)
    (query : SourceCurrentAllocatedScanWorker.query p h n values record.paths later fourth = .done value queried queryMemo)
    (decision : SourceCurrentAllocatedScanWorker.decision p h budget record.paths value queried queryMemo = .done true after saved) :
    scan g s p h n budget values (record :: records) before memo = .done (some record.paths, []) after saved := by
  simp only [scan, primary, secondary, query, decision, SourceCurrentAllocatedScanWorker.Outcome.bind,
    ite_true, Bool.false_eq_true, ite_false]

-- Successful projection retains the stopped paths, all selected paths, checked state, and memo.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (records kept : List Record)
    (before after : Checked width) (memo saved : Memo)
    (actual : scan g s p h n budget values records before memo = .done (stopped, kept) after saved) :
    SourceCurrentAllocatedScanWorker.scan g s p h n budget values (records.map Record.paths) before memo =
      .done (stopped, kept.map Record.paths) after saved := by
  rw [← scan_mapPaths]
  exact congrArg mapPaths actual

-- Failure projection retains every nested selected tag and all state fields.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before after : Checked width) (memo saved : Memo)
    (actual : scan g s p h n budget values records before memo = .failed fault after saved) :
    SourceCurrentAllocatedScanWorker.scan g s p h n budget values (records.map Record.paths) before memo =
      .failed fault after saved := by
  rw [← scan_mapPaths]
  exact congrArg mapPaths actual

-- Different successful bounds identify exact records, equality operations, and the fourth memo.
example {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)}
    {records : List Record} {before after later : Checked width} {memo saved current : Memo} {first second : Result}
    (one : scan g s p h n budget values records before memo = .done first after saved)
    (two : scan G S P H N budget values records before memo = .done second later current) :
    first = second ∧ after.operations = later.operations ∧ saved = current := by
  obtain ⟨result, state, fourth⟩ := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique one two
  exact ⟨result, congrArg SourceEqualityNativeDemand.State.operations state, fourth⟩
end MicroCFTA.RecordScanIndependentProbes
