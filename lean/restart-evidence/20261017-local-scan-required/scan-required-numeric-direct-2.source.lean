import MicroCFTA.SourceCurrentRecordScanNumeric
import MicroCFTA.SourceCurrentRequiredInitialNumeric
import MicroCFTA.SourceCurrentScanRequiredWorker
import MicroCFTA.SourceCurrentScanRequiredForecast
import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

/-!
# Complete Scan and Required preparation from initial numeric resources

The actual Scan selects original record occurrences. A stopped return
erases the original forest. Otherwise its false primary certificates
construct Required at that exact return. The initial record list bounds
every possible selection. No finite input cap is required.
-/
namespace MicroCFTA.SourceCurrentScanRequiredNumeric
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder (Record Coherent)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "fuel" => SourceCurrentScanRequiredForecast.fuel
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Exact preparation follows only the reached Scan branch and retains its original records. -/
inductive Execution (budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) :
    Option Class → List Record → List (Value Symbol Guard) → Checked width → Fourth → Prop where
  /-- A stopped Scan erases the original forest without running Required. -/
  | stopped {paths kept after saved}
      (scan : Scan budget source reaches values (records.map Record.paths) before fourth
        (some paths) (kept.map Record.paths) after saved) (retained : Retained scan records kept) :
      Execution budget records values before fourth (some paths) kept (EqualityLeafProjectionRuntimeEmpty.erase values) after saved
  /-- A successful Scan runs the selected original paths at its actual returned heap. -/
  | prepared {kept middle saved results heap r h}
      (scan : Scan budget source reaches values (records.map Record.paths) before fourth
        none (kept.map Record.paths) middle saved) (retained : Retained scan records kept)
      (required : SourceEqualityRequiredExecution.requireAll r h
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle.native.machine.heap = .done results heap) :
      Execution budget records values before fourth none kept results (advanceHeap middle heap) saved

/-- Strict source reads pass the same actual global memo bundle through preparation. -/
inductive Reads : {budget : Nat} → {records : List Record} → {values results : List (Value Symbol Guard)} →
    {before after : Checked width} → {fourth saved : Fourth} → {outcome : Option Class} → {kept : List Record} →
    Execution budget records values before fourth outcome kept results after saved → Memos → Memos → Prop where
  /-- A stopped Scan supplies the complete reached source reads. -/
  | stopped {scan retained memos final} (reads : ScanReads scan memos final) :
      Reads (Execution.stopped scan retained) memos final
  /-- Required starts with the exact global bundle returned by its own Scan. -/
  | prepared {budget : Nat} {records kept : List Record} {values results : List (Value Symbol Guard)}
      {before middle : Checked width} {fourth saved : Fourth} {heap : State Symbol Guard} {r h : Nat}
      {scan : Scan budget source reaches values (records.map Record.paths) before fourth none (kept.map Record.paths) middle saved}
      {retained : Retained scan records kept}
      {required : SourceEqualityRequiredExecution.requireAll r h (SourceEqualitySelectedRequired.paths (kept.map Record.paths))
        values middle.native.machine.heap = .done results heap} {memos scanMemos final : Memos}
      (first : ScanReads scan memos scanMemos)
      (second : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths (kept.map Record.paths))
        values results middle.native.machine.heap heap scanMemos final) :
      Reads (Execution.prepared scan retained required) memos final

/-- One constructed preparation retains its full caller, selected domains, language, and exact replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Caller width) (memos : Memos) (outcome : Option Class) (kept : List Record)
    (results : List (Value Symbol Guard)) (after : Checked width) (saved : Fourth) (final : Memos) : Prop where
  /-- The same returned forest and checked state follow the exact source preparation. -/
  actual : Execution budget records values before.checked before.fourth outcome kept results after saved
  /-- The source reads use the actual execution and its returned global bundle. -/
  reads : Reads actual memos final
  /-- The complete query Frame uses the same returned inventory as Post. -/
  frame : Frame formulas solver inventory after
  /-- The initial record schedule bounds the complete preparation return. -/
  fits : Fits (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
    (guards before.checked.native.machine.heap) profile) after
  /-- Both outer tables and Merge retain their exact initial values in the returned caller. -/
  post : Post formulas solver inventory before (advance before after saved before.merge) final
  /-- Every original value remains available in the returned heap. -/
  originals : Values after.native.machine.heap values
  /-- Every returned value is available in that same heap. -/
  available : Values after.native.machine.heap results
  /-- Both source branches preserve the number of original child slots. -/
  length : results.length = values.length
  /-- Selected records retain source order and repeated occurrences. -/
  selected : kept.Sublist records
  /-- Successful preparation supplies every selected class domain. -/
  domains : outcome = none → ∀ record ∈ kept, ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results
  /-- A stopped class refutes every accepted original forest. -/
  rejected : SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values (records.map Record.paths) outcome
  /-- Preparation narrows the forest and preserves each original class-satisfying term. -/
  language : ∀ ambient symbol terms,
    (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    ((∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
      (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))
  /-- Initial source facts derive the older Scan range interface. -/
  ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget source reaches values
    (records.map Record.paths) before.checked before.fourth
  /-- All six preparation fuels can increase independently with the same complete return. -/
  run : ∀ g s r p h n, fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ g →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ s →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ r →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ p →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ h →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ n →
    SourceCurrentScanRequiredWorker.prepare g s r p h n budget records values before.checked before.fourth before.merge =
      .done (outcome, kept, results) after saved before.merge

/-- Initial invariants construct the complete uncapped preparation and its same-inventory caller Post. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentScanNumericForecast.Reserved bits budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile) :
    ∃ outcome kept results after saved next final,
      Receipt formulas solver next profile budget records values before memos outcome kept results after saved final := by
  obtain ⟨outcome, kept, middle, saved, next, scanMemos, scanned, retained, scanReads, scanPost,
      sublist, fields, sound, _nodes, _edges, _merge, _fourth, scanDone⟩ :=
    SourceCurrentRecordScanNumeric.complete formulas solver inventory budget values records before memos initial frame profile fits
      available proper coherent active reserved
  have pathsProper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact active record present
  have scanLimit := SourceCurrentScanRequiredForecast.scan_fuel budget values.length records
    (guards before.checked.native.machine.heap) profile
  cases outcome with
  | some paths =>
      refine ⟨some paths, kept, EqualityLeafProjectionRuntimeEmpty.erase values, middle, saved, next, scanMemos,
        .stopped scanned.actual retained, .stopped scanReads, scanned.frame,
        scanned.fits.mono (SourceCurrentScanRequiredForecast.scan_le _ _ _ _ _), scanPost,
        scanned.available, (SourceEqualityEmptyPropagation.erased_scope middle.native.machine.heap values).1,
        List.length_map _, sublist, ?_, sound, ?_, scanned.ranges, ?_⟩
      · intro impossible
        cases impossible
      · intro ambient symbol terms
        have narrows : All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
            (EqualityLeafProjectionRuntimeEmpty.erase values) terms →
            All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms := by
          cases values with
          | nil => exact id
          | cons first rest =>
              intro accepted
              cases accepted with
              | cons impossible _ => simp only [InternedGuardedLanguage.meaning] at impossible
        refine ⟨narrows, fun satisfied => ⟨narrows, ?_⟩⟩
        intro accepted
        obtain ⟨record, present, same⟩ := List.mem_map.mp (sound paths rfl).1
        exact False.elim ((sound paths rfl).2 ambient symbol terms accepted (same ▸ satisfied record present))
      · intro g s r p h n enoughG enoughS _enoughR enoughP enoughH enoughN
        have done := scanDone g s p h n (Nat.le_trans scanLimit enoughG) (Nat.le_trans scanLimit enoughS)
          (Nat.le_trans scanLimit enoughP) (Nat.le_trans scanLimit enoughH) (Nat.le_trans scanLimit enoughN)
        simp only [SourceCurrentScanRequiredWorker.prepare, SourceCurrentAllocatedLocalWorker.scan, done,
          SourceCurrentAllocatedLocalWorker.Outcome.bind]
  | none =>
      have primary := SourceCurrentConjunctionRequired.selected_primary formulas solver inventory scanned.actual
        initial.ready initial.admitted available pathsProper pathsActive initial.correct scanned.ranges
      have selectedProper : ∀ path ∈ (kept.map Record.paths).flatten, path ≠ [] := by
        intro path member
        obtain ⟨paths, present, included⟩ := List.mem_flatten.mp member
        obtain ⟨record, keptIn, rfl⟩ := List.mem_map.mp present
        exact proper record (sublist.subset keptIn) path included
      obtain ⟨results, heap, final, required, requiredReads, returned, requiredPost, length, requiredFits,
          _nodes, _edges, _fourth, _merge, requiredDone, stable⟩ :=
        SourceCurrentRequiredInitialNumeric.caller formulas solver next source reaches (kept.map Record.paths)
          values (advance before middle saved before.merge) scanMemos scanPost.context scanned.frame
          (SourceCurrentScanRequiredForecast.scanProfile budget values.length records (guards before.checked.native.machine.heap) profile)
          scanned.fits scanned.available selectedProper primary
      have afterFits := requiredFits.mono (SourceCurrentInitialSelectionForecast.required_selected sublist values.length _)
      have post : Post formulas solver next before (advance before (advanceHeap middle heap) saved before.merge) final :=
        scanPost.trans requiredPost
      refine ⟨none, kept, results, advanceHeap middle heap, saved, next, final,
        .prepared scanned.actual retained requiredDone, .prepared scanReads requiredReads, returned, afterFits, post,
        (fun value member => required.effects.keeps.available value (scanned.available value member)),
        required.resident, length, sublist, ?_, sound, ?_, scanned.ranges, ?_⟩
      · intro _ record member path included
        exact required.paths path (List.mem_flatten.mpr ⟨record.paths, List.mem_map.mpr ⟨record, member, rfl⟩, included⟩)
      · intro ambient symbol terms
        have language := required.language (SourceEqualityPCSGuard.holds formulas solver) ambient terms
        refine ⟨fun accepted => (language.mp accepted).1, ?_⟩
        intro satisfied
        have selectedActive : ∀ paths ∈ kept.map Record.paths, Nontrivial paths := by
          intro paths member
          obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
          exact (fields record present).2
        have selectedSatisfied : ∀ paths ∈ kept.map Record.paths, ClassSat (.node symbol terms) paths := by
          intro paths member
          obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
          exact satisfied record (sublist.subset present)
        have needed := SourceCurrentConjunctionRequiredClassPass.satisfied_required _ symbol terms selectedActive selectedSatisfied
        exact language.trans ⟨And.left, fun accepted => ⟨accepted, needed⟩⟩
      · intro g s r p h n enoughG enoughS enoughR enoughP enoughH enoughN
        have done := scanDone g s p h n (Nat.le_trans scanLimit enoughG) (Nat.le_trans scanLimit enoughS)
          (Nat.le_trans scanLimit enoughP) (Nat.le_trans scanLimit enoughH) (Nat.le_trans scanLimit enoughN)
        have prepared := stable r h
          (Nat.le_trans (SourceCurrentScanRequiredForecast.required_worker sublist _ _ _ _) enoughR)
          (Nat.le_trans (SourceCurrentScanRequiredForecast.required_reader sublist _ _ _ _) enoughH)
        simp only [SourceCurrentScanRequiredWorker.prepare, SourceCurrentAllocatedLocalWorker.scan, done,
          SourceCurrentAllocatedLocalWorker.Outcome.bind, SourceCurrentAllocatedLocalWorker.required, prepared]

end MicroCFTA.SourceCurrentScanRequiredNumeric
