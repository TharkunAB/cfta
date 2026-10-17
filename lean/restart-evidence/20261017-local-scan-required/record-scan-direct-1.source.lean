import MicroCFTA.SourceCurrentScanCallerNumeric
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual

/-!
# Initial numeric Scans with original class records

The path Scan constructs its own numeric receipt. Path projection then
derives success of the literal record worker at the same five bounds.
Positional retention identifies the original record occurrences. It does
not require distinct records or distinct path lists.
-/
namespace MicroCFTA.SourceCurrentRecordScanNumeric
open EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "recordScan" => SourceCurrentAllocatedRecordScanWorker.scan
local notation "pathScan" => SourceCurrentAllocatedScanWorker.scan
local notation "fuel" => SourceCurrentScanNumericForecast.fuel
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

/-- A successful path projection gives a literal record return at the same bounds. -/
theorem of_paths {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records : List Record} {before after : Checked width} {memo saved : Memo}
    {outcome : Option Class} {selected : Constraints}
    (done : pathScan g s p h n budget values (records.map Record.paths) before memo =
      .done (outcome, selected) after saved) :
    ∃ kept, kept.map Record.paths = selected ∧
      recordScan g s p h n budget values records before memo = .done (outcome, kept) after saved := by
  have projected := (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths
    g s p h n budget values records before memo).trans done
  cases actual : recordScan g s p h n budget values records before memo with
  | failed fault heap current =>
      rw [actual] at projected
      cases projected
  | done result heap current =>
      obtain ⟨stopped, kept⟩ := result
      rw [actual] at projected
      obtain ⟨same, rfl, rfl⟩ := SourceCurrentAllocatedScanWorker.Outcome.done.inj projected
      obtain ⟨rfl, paths⟩ := Prod.mk.inj same
      exact ⟨kept, paths, actual⟩

/-- Positional retention identifies the exact record occurrences at the computed bounds. -/
theorem retained_run {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {records kept : List Record} {before after : Checked width} {memo saved : Memo}
    {outcome : Option Class}
    {actual : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map Record.paths) before memo outcome (kept.map Record.paths) after saved}
    (retained : Retained actual records kept)
    (done : pathScan g s p h n budget values (records.map Record.paths) before memo =
      .done (outcome, kept.map Record.paths) after saved) :
    recordScan g s p h n budget values records before memo = .done (outcome, kept) after saved := by
  obtain ⟨other, _paths, returned⟩ := of_paths done
  obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
  have known := stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)
  have same := SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique known returned
  have aligned : kept = other := congrArg Prod.snd same.1
  simpa only [← aligned] using returned

/-- Initial caller resources construct the record Scan and every larger five-fuel replay. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentScanNumericForecast.Reserved bits budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile) :
    ∃ outcome kept after saved next final,
      ∃ receipt : SourceCurrentScanNumeric.Receipt formulas solver (guards before.checked.native.machine.heap)
          profile budget values (records.map Record.paths) before.checked before.fourth
          outcome (kept.map Record.paths) after saved next,
        Retained receipt.actual records kept ∧ ScanReads receipt.actual memos final ∧
        Post formulas solver next before (advance before after saved before.merge) final ∧
        kept.Sublist records ∧ (∀ record ∈ kept, Coherent record ∧ Nontrivial record.paths) ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values (records.map Record.paths) outcome ∧
        (advance before after saved before.merge).nodeResults = before.nodeResults ∧
        (advance before after saved before.merge).edgeResults = before.edgeResults ∧
        (advance before after saved before.merge).merge = before.merge ∧
        (advance before after saved before.merge).fourth = saved ∧
        ∀ g s p h n, fuel budget values.length (records.map Record.paths)
            (guards before.checked.native.machine.heap) profile ≤ g →
          fuel budget values.length (records.map Record.paths) (guards before.checked.native.machine.heap) profile ≤ s →
          fuel budget values.length (records.map Record.paths) (guards before.checked.native.machine.heap) profile ≤ p →
          fuel budget values.length (records.map Record.paths) (guards before.checked.native.machine.heap) profile ≤ h →
          fuel budget values.length (records.map Record.paths) (guards before.checked.native.machine.heap) profile ≤ n →
          recordScan g s p h n budget values records before.checked before.fourth =
            .done (outcome, kept) after saved := by
  have pathsProper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
    exact proper record included
  have pathsActive : ∀ paths ∈ records.map Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
    exact active record included
  obtain ⟨outcome, selected, after, saved, next, final, receipt, reads, post, _selected,
    sound, nodeTable, edgeTable, mergeTable, fourthTable⟩ :=
    SourceCurrentScanCallerNumeric.complete formulas solver inventory budget values (records.map Record.paths)
      before memos initial frame profile fits available pathsProper pathsActive reserved
  obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records receipt.actual
  have fields := retained.fields
  have aligned := fields.2
  subst selected
  refine ⟨outcome, kept, after, saved, next, final, receipt, retained, reads, post, fields.1,
    (fun record member => ⟨coherent record (fields.1.subset member), active record (fields.1.subset member)⟩),
    sound, nodeTable, edgeTable, mergeTable, fourthTable, ?_⟩
  intro g s p h n enoughG enoughS enoughP enoughH enoughN
  exact retained_run retained (receipt.run g s p h n enoughG enoughS enoughP enoughH enoughN)

end MicroCFTA.SourceCurrentRecordScanNumeric
