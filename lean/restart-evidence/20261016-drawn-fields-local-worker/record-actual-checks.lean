import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.scan_complete
#check @MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.scan_complete
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.sound
#check @MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.sound
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.verified
#check @MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.finite
#check @MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual.finite

namespace RecordActualChecks
open MicroCFTA
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
open SourceCurrentAllocatedScanWorkerCompletion (StableRun)
open SourceCurrentAllocatedRecordScanWorker (scan)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem empty_stable (budget : Nat) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    StableRun (fun g s p h n => scan g s p h n budget values [] before memo) (none, []) before memo :=
  SourceCurrentAllocatedRecordScanWorkerActual.scan_complete (Retained.nil (budget := budget) (values := values))

theorem equal_paths_keep_both (budget : Nat) (values : List (Value Symbol Guard))
    (first second : Record) (same : first.paths = second.paths) (before : Checked width)
    (heap later : State Symbol Guard) (memo : Memo)
    (one : EndpointStatefulGateTrace.ClassTrace source reaches values first.paths
      before.native.machine.heap false heap)
    (two : EndpointStatefulGateTrace.ClassTrace source reaches values first.paths heap false later) :
    StableRun (fun g s p h n => scan g s p h n budget values [first, second] before memo)
      (none, [first, second]) (advanceHeap (advanceHeap before heap) later) memo := by
  exact SourceCurrentAllocatedRecordScanWorkerActual.scan_complete
    (Retained.selected (primary := one) rfl
      (Retained.selected (primary := two) same.symm Retained.nil))

theorem selected_prefix_before_stop {budget : Nat} {values : List (Value Symbol Guard)}
    (head : Record) (records : List Record) (stopped : Class) {classes : Constraints}
    {before after : Checked width} {heap : State Symbol Guard} {memo saved : Memo}
    (primary : EndpointStatefulGateTrace.ClassTrace source reaches values head.paths before.native.machine.heap false heap)
    (tail : Scan budget source reaches values classes (advanceHeap before heap) memo (some stopped) [] after saved)
    (retained : Retained tail records []) :
    StableRun (fun g s p h n => scan g s p h n budget values (head :: records) before memo)
      (some stopped, [head]) after saved :=
  SourceCurrentAllocatedRecordScanWorkerActual.scan_complete (.selected (primary := primary) rfl retained)

theorem supplied_positions (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s p h n budget : Nat} {values : List (Value Symbol Guard)} {records kept : List Record}
    {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (done : scan g s p h n budget values records before memo = .done (outcome, kept) after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before memo) :
    kept.Sublist records ∧ ∃ actual : Scan budget source reaches values (records.map Record.paths) before memo
      outcome (kept.map Record.paths) after saved, Retained actual records kept := by
  obtain ⟨actual, retained⟩ := SourceCurrentAllocatedRecordScanWorkerActual.sound
    formulas solver done ready available proper correct ranges
  exact ⟨retained.fields.1, actual, retained⟩

theorem finite_literal_return (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ records.map Record.paths, Nontrivial paths)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before.checked before.fourth) :
    ∃ g s p h n outcome kept after saved next final,
      scan g s p h n budget values records before.checked before.fourth = .done (outcome, kept) after saved ∧
      ∃ actual : Scan budget source reaches values (records.map Record.paths) before.checked before.fourth
        outcome (kept.map Record.paths) after saved,
        Retained actual records kept ∧ ScanReads actual memos final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        kept.Sublist records := by
  obtain ⟨outcome, kept, after, saved, next, final, ⟨g, s, p, h, n, stable⟩,
    actual, retained, reads, post, _, sublist, _⟩ :=
    SourceCurrentAllocatedRecordScanWorkerActual.finite formulas solver budget values records
      initial available proper active ranges
  exact ⟨g, s, p, h, n, outcome, kept, after, saved, next, final,
    stable g s p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    actual, retained, reads, post, sublist⟩

theorem actual_stop_refutes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {paths : Class} {before : Caller width}
    {after : Checked width} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ records.map Record.paths, Nontrivial paths)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before.checked before.fourth)
    (done : scan g s p h n budget values records before.checked before.fourth = .done (some paths, kept) after saved) :
    kept.Sublist records ∧ paths ∈ records.map Record.paths ∧
      ∀ ambient symbol terms,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        ¬ClassSat (.node symbol terms) paths := by
  obtain ⟨_, _, _, _, _, _, _, sublist, stopped⟩ :=
    SourceCurrentAllocatedRecordScanWorkerActual.verified formulas solver initial available proper active ranges done
  exact ⟨sublist, stopped paths rfl⟩

end RecordActualChecks

#print axioms RecordActualChecks.empty_stable
#check @RecordActualChecks.empty_stable
#print axioms RecordActualChecks.equal_paths_keep_both
#check @RecordActualChecks.equal_paths_keep_both
#print axioms RecordActualChecks.selected_prefix_before_stop
#check @RecordActualChecks.selected_prefix_before_stop
#print axioms RecordActualChecks.supplied_positions
#check @RecordActualChecks.supplied_positions
#print axioms RecordActualChecks.finite_literal_return
#check @RecordActualChecks.finite_literal_return
#print axioms RecordActualChecks.actual_stop_refutes
#check @RecordActualChecks.actual_stop_refutes
