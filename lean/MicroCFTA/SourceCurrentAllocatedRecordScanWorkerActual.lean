import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedScanWorkerActual
import MicroCFTA.SourceCurrentConjunctionSelectedRecords

/-!
# Literal Scan receipts for exact original record occurrences

The positional receipt supplies stable bounds for the literal record worker.
The worker retains each original record at its actual selected branch.
Successful execution identifies the same Scan and positional receipt.
The caller adapter derives strict reads and full returned invariants.
Repeated paths need no uniqueness assumption. Host demand remains separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
open SourceCurrentAllocatedScanWorkerCompletion (StableRun)
open SourceCurrentAllocatedRecordScanWorker (scan select)
open SourceCurrentAllocatedScanWorker (gate query decision Outcome)
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

/-- Actual positional retention supplies stable execution of the exact original records. -/
theorem scan_complete {budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    {actual : Scan budget source reaches values classes before memo outcome selected after saved}
    (retained : Retained actual records kept) :
    StableRun (fun g s p h n => scan g s p h n budget values records before memo)
      (outcome, kept) after saved := by
  induction retained with
  | nil => exact ⟨0, 0, 0, 0, 0, by intros; rfl⟩
  | @selected paths classes selected outcome before after heap memo saved primary rest record records kept head tail ih =>
      cases head
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨laterG, s, p, h, n, tailDone⟩ := ih
      refine ⟨max g laterG, s, p, h, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have later := tailDone G S P H N (by omega) enoughS enoughP enoughH enoughN
      simp only [scan, gate, ite_true, first, Outcome.bind, Bool.false_eq_true, ite_false, later, select]
  | @skipped paths classes selected outcome before after heap anchor memo saved primary secondary rest record records kept head tail ih =>
      cases head
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨laterG, laterS, p, h, n, tailDone⟩ := ih
      refine ⟨max g laterG, max s laterS, p, h, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have second := secondaryDone S (by omega)
      have later := tailDone G S P H N (by omega) (by omega) enoughP enoughH enoughN
      simp only [scan, gate, Bool.false_eq_true, ite_true, ite_false, first, second, Outcome.bind, later]
  | @continued paths classes selected outcome before middle after later heap anchor queryValue memo savedMemo saved
      primary secondary seeded decision rest record records kept head tail ih =>
      cases head
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨p, h, n, queryDone⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete seeded
      obtain ⟨decisionP, decisionH, checkedDone⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete decision
      obtain ⟨laterG, laterS, laterP, laterH, laterN, tailDone⟩ := ih
      refine ⟨max g laterG, max s laterS, max p (max decisionP laterP),
        max h (max decisionH laterH), max n laterN, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have second := secondaryDone S (by omega)
      have projected := queryDone P H N (by omega) (by omega) (by omega)
      have checked := SourceCurrentAllocatedConjunctionWorker.call_lift (before := middle)
        (checkedDone P H (by omega) (by omega))
      have next := tailDone G S P H N (by omega) (by omega) (by omega) (by omega) (by omega)
      simp only [scan, gate, ite_true, ite_false, first, second, Outcome.bind,
        Bool.false_eq_true, query, projected, SourceCurrentAllocatedScanWorker.decision, checked, next]
  | @stopped paths classes before middle later heap anchor queryValue memo saved primary secondary seeded decision record records head remaining =>
      cases head
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨p, h, n, queryDone⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete seeded
      obtain ⟨decisionP, decisionH, checkedDone⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete decision
      refine ⟨g, s, max p decisionP, max h decisionH, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G enoughG
      have second := secondaryDone S enoughS
      have projected := queryDone P H N (by omega) (by omega) enoughN
      have checked := SourceCurrentAllocatedConjunctionWorker.call_lift (before := middle)
        (checkedDone P H (by omega) (by omega))
      simp only [scan, gate, ite_true, ite_false, first, second, Outcome.bind,
        Bool.false_eq_true, query, projected, SourceCurrentAllocatedScanWorker.decision, checked]

/-- Literal success derives the same current Scan and exact retained record occurrences. -/
theorem sound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s p h n budget : Nat} {values : List (Value Symbol Guard)} {records kept : List Record}
    {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (done : scan g s p h n budget values records before memo = .done (outcome, kept) after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before memo) :
    ∃ actual : Scan budget source reaches values (records.map Record.paths) before memo
        outcome (kept.map Record.paths) after saved,
      Retained actual records kept := by
  have projected := congrArg SourceCurrentAllocatedRecordScanWorker.mapPaths done
  rw [SourceCurrentAllocatedRecordScanWorker.scan_mapPaths] at projected
  have actual := SourceCurrentAllocatedScanWorkerActual.sound formulas solver projected ready available proper correct ranges
  obtain ⟨chosen, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actual
  obtain ⟨G, S, P, H, N, stable⟩ := scan_complete retained
  obtain ⟨same, _, _⟩ := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique
    (stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  have aligned : chosen = kept := congrArg Prod.snd same
  subst chosen
  exact ⟨actual, retained⟩

/-- A supplied record return derives strict reads and the full caller at that same state. -/
theorem verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {outcome : Option Class} {before : Caller width}
    {after : Checked width} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ records.map Record.paths, Nontrivial paths)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before.checked before.fourth)
    (done : scan g s p h n budget values records before.checked before.fourth = .done (outcome, kept) after saved) :
    ∃ next final,
      ∃ actual : Scan budget source reaches values (records.map Record.paths) before.checked before.fourth
          outcome (kept.map Record.paths) after saved,
        Retained actual records kept ∧ ScanReads actual memos final ∧
        Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        Values after.native.machine.heap values ∧ kept.Sublist records ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values (records.map Record.paths) outcome := by
  obtain ⟨actual, retained⟩ := sound formulas solver done initial.ready available proper initial.correct ranges
  obtain ⟨next, final, reads, post, resident, _, stopped⟩ :=
    SourceCurrentAllocatedScanCaller.actual formulas solver actual initial available proper active ranges
  exact ⟨next, final, actual, retained, reads, post, resident, retained.fields.1, stopped⟩

/-- Legitimate entry constructs stable record execution, positional retention, and full return facts. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ records.map Record.paths, Nontrivial paths)
    (ranges : Ranges budget source reaches values (records.map Record.paths) before.checked before.fourth) :
    ∃ outcome kept after saved next final,
      StableRun (fun g s p h n => scan g s p h n budget values records before.checked before.fourth)
        (outcome, kept) after saved ∧
      ∃ actual : Scan budget source reaches values (records.map Record.paths) before.checked before.fourth
          outcome (kept.map Record.paths) after saved,
        Retained actual records kept ∧ ScanReads actual memos final ∧
        Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        Values after.native.machine.heap values ∧ kept.Sublist records ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values (records.map Record.paths) outcome := by
  obtain ⟨outcome, selected, after, saved, next, final, actual, reads, post, resident, _, stopped⟩ :=
    SourceCurrentAllocatedScanCaller.finite formulas solver budget values (records.map Record.paths)
      initial available proper active ranges
  obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actual
  have aligned := retained.fields.2
  subst selected
  exact ⟨outcome, kept, after, saved, next, final, scan_complete retained, actual, retained,
    reads, post, resident, retained.fields.1, stopped⟩

end MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual
