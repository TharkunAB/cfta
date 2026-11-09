import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceCurrentRequiredInitialNumeric
import MicroCFTA.SourceCurrentSharedScanRequiredWorker
import MicroCFTA.SourceCurrentSharedScanRequiredForecast
import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

/-!
# Actual shared Scan and selected Required preparation

The shared Scan retains its original selected record occurrences. Its
derived primary certificates construct Required at that exact returned
state. Stopped branches erase the forest and skip Required. Initial
resources bound all six preparation fuels. No historical Scan or future
range, support or completed execution is an input.
-/
namespace MicroCFTA.SourceCurrentSharedScanRequiredNumeric
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder (Record Coherent)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "fuel" => SourceCurrentSharedScanRequiredForecast.fuel
local notation "recordScan" => SourceCurrentAllocatedSharedRecordScanWorker.scan
local notation "ScanReads" => SourceCurrentSharedScanCallerNumeric.ScanReads
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- The actual shared record scan selects only its literal stopped or Required continuation. -/
inductive Execution (budget : Nat) (records : List Record) (values : List Node)
    (before : Checked width) (fourth : Fourth) :
    Option Class → List Record → List Node → Checked width → Fourth → Prop where
  | stopped {paths kept after saved g s p h n}
      (observed : recordScan g s p h n budget values records before fourth = .done (some paths, kept) after saved) :
      Execution budget records values before fourth (some paths) kept (EqualityLeafProjectionRuntimeEmpty.erase values) after saved
  | prepared {kept middle saved results heap g s p h n r read}
      (observed : recordScan g s p h n budget values records before fourth = .done (none, kept) middle saved)
      (required : SourceEqualityRequiredExecution.requireAll r read
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle.native.machine.heap = .done results heap) :
      Execution budget records values before fourth none kept results (advanceHeap middle heap) saved

/-- Source reads retain the actual shared Scan bundle before the selected Required reads. -/
inductive Reads : {budget : Nat} → {records : List Record} → {values results : List Node} →
    {before after : Checked width} → {fourth saved : Fourth} → {outcome : Option Class} → {kept : List Record} →
    Execution budget records values before fourth outcome kept results after saved → Memos → Memos → Prop where
  | stopped {budget records values before fourth paths kept after saved g s p h n memos final}
      {observed : recordScan g s p h n budget values records before fourth = .done (some paths, kept) after saved}
      (reads : ScanReads budget values records before fourth (some paths) kept after saved memos final) :
      Reads (Execution.stopped observed) memos final
  | prepared {budget records values before fourth kept middle saved results heap g s p h n r read}
      {observed : recordScan g s p h n budget values records before fourth = .done (none, kept) middle saved}
      {required : SourceEqualityRequiredExecution.requireAll r read
        (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle.native.machine.heap = .done results heap}
      {memos scanMemos final : Memos}
      (first : ScanReads budget values records before fourth none kept middle saved memos scanMemos)
      (second : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths (kept.map Record.paths))
        values results middle.native.machine.heap heap scanMemos final) :
      Reads (Execution.prepared observed required) memos final

/-- One actual preparation retains its caller, selected original domains and computed replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (records : List Record) (values : List Node)
    (before : Caller width) (memos : Memos) (outcome : Option Class) (kept : List Record)
    (results : List Node) (after : Checked width) (saved : Fourth) (final : Memos) : Prop where
  actual : Execution budget records values before.checked before.fourth outcome kept results after saved
  reads : Reads actual memos final
  frame : Frame formulas solver inventory after
  fits : Fits (SourceCurrentSharedScanRequiredForecast.finalProfile budget values.length records
    (guards before.checked.native.machine.heap) profile) after
  post : Post formulas solver inventory before (advance before after saved before.merge) final
  originals : Values after.native.machine.heap values
  available : Values after.native.machine.heap results
  length : results.length = values.length
  selected : kept.Sublist records
  fields : ∀ record ∈ kept, Coherent record ∧ Nontrivial record.paths
  domains : outcome = none → ∀ record ∈ kept, ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results
  rejected : SourceCurrentSharedScanCallerNumeric.StoppedSound formulas solver values records outcome
  language : ∀ ambient symbol terms,
    (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    ((∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
      (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))
  run : ∀ g s r p h n,
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ g →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ s →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ r →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ p →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ h →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ n →
    SourceCurrentSharedScanRequiredWorker.prepare g s r p h n budget records values before.checked before.fourth before.merge =
      .done (outcome, kept, results) after saved before.merge

/-- Original caller facts derive the actual shared preparation without a future Scan or Required supplier. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List Node) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentSharedScanNumericForecast.Reserved bits budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile) :
    ∃ outcome kept results after saved next final,
      Receipt formulas solver next profile budget records values before memos outcome kept results after saved final := by
  obtain ⟨outcome, kept, middle, saved, next, scanMemos, scanned⟩ :=
    SourceCurrentSharedScanCallerNumeric.complete formulas solver inventory (guards before.checked.native.machine.heap)
      budget values records before memos initial frame profile fits available proper active reserved
      (SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
        initial.ready.semantic.ready.semantic.1.normal.facts)
  let scanFuel := SourceCurrentSharedScanNumericForecast.fuel budget values.length (records.map Record.paths)
    (guards before.checked.native.machine.heap) profile
  have scanDone := scanned.run scanFuel scanFuel scanFuel scanFuel scanFuel
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have selectedFields : ∀ record ∈ kept, Coherent record ∧ Nontrivial record.paths :=
    fun record member => ⟨coherent record (scanned.selected.subset member), active record (scanned.selected.subset member)⟩
  have scanLimit := SourceCurrentSharedScanRequiredForecast.scan_fuel budget values.length records
    (guards before.checked.native.machine.heap) profile
  cases outcome with
  | some paths =>
      refine ⟨some paths, kept, EqualityLeafProjectionRuntimeEmpty.erase values, middle, saved, next, scanMemos,
        .stopped scanDone, .stopped (observed := scanDone) scanned.reads, scanned.frame,
        scanned.fits.mono (SourceCurrentSharedScanRequiredForecast.scan_le _ _ _ _ _), scanned.post,
        scanned.available, (SourceEqualityEmptyPropagation.erased_scope middle.native.machine.heap values).1,
        List.length_map _, scanned.selected, selectedFields, ?_, scanned.sound, ?_, ?_⟩
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
        obtain ⟨record, present, same⟩ := List.mem_map.mp (scanned.sound paths rfl).1
        exact False.elim ((scanned.sound paths rfl).2 ambient symbol terms accepted (same ▸ satisfied record present))
      · intro g s r p h n enoughG enoughS _enoughR enoughP enoughH enoughN
        have done := scanned.run g s p h n (Nat.le_trans scanLimit enoughG) (Nat.le_trans scanLimit enoughS)
          (Nat.le_trans scanLimit enoughP) (Nat.le_trans scanLimit enoughH) (Nat.le_trans scanLimit enoughN)
        simp only [SourceCurrentSharedScanRequiredWorker.prepare, SourceCurrentAllocatedSharedLocalWorker.scan, done,
          SourceCurrentAllocatedSharedLocalWorker.Outcome.bind]
  | none =>
      have selectedProper : ∀ path ∈ (kept.map Record.paths).flatten, path ≠ [] := by
        intro path member
        obtain ⟨paths, present, included⟩ := List.mem_flatten.mp member
        obtain ⟨record, keptIn, rfl⟩ := List.mem_map.mp present
        exact proper record (scanned.selected.subset keptIn) path included
      have primary : ∀ paths ∈ kept.map Record.paths,
          EndpointStatefulGateTrace.ClassTrace source reaches values paths middle.native.machine.heap false middle.native.machine.heap := by
        intro paths member
        obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
        exact scanned.primary record present
      obtain ⟨results, heap, final, required, requiredReads, returned, requiredPost, length, requiredFits,
          _nodes, _edges, _fourth, _merge, requiredDone, stable⟩ :=
        SourceCurrentRequiredInitialNumeric.caller formulas solver next source reaches (kept.map Record.paths)
          values (advance before middle saved before.merge) scanMemos scanned.post.context scanned.frame
          (SourceCurrentSharedScanRequiredForecast.scanProfile budget values.length records
            (guards before.checked.native.machine.heap) profile) scanned.fits scanned.available selectedProper primary
      have afterFits := requiredFits.mono (SourceCurrentInitialSelectionForecast.required_selected scanned.selected values.length _)
      have post : Post formulas solver next before (advance before (advanceHeap middle heap) saved before.merge) final :=
        scanned.post.trans requiredPost
      refine ⟨none, kept, results, advanceHeap middle heap, saved, next, final,
        .prepared scanDone requiredDone, .prepared (observed := scanDone) (required := requiredDone) scanned.reads requiredReads,
        returned, afterFits, post,
        (fun value member => required.effects.keeps.available value (scanned.available value member)),
        required.resident, length, scanned.selected, selectedFields, ?_, scanned.sound, ?_, ?_⟩
      · intro _ record member path included
        exact required.paths path (List.mem_flatten.mpr ⟨record.paths, List.mem_map.mpr ⟨record, member, rfl⟩, included⟩)
      · intro ambient symbol terms
        have language := required.language (SourceEqualityPCSGuard.holds formulas solver) ambient terms
        refine ⟨fun accepted => (language.mp accepted).1, ?_⟩
        intro satisfied
        have selectedActive : ∀ paths ∈ kept.map Record.paths, Nontrivial paths := by
          intro paths member
          obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
          exact (selectedFields record present).2
        have selectedSatisfied : ∀ paths ∈ kept.map Record.paths, ClassSat (.node symbol terms) paths := by
          intro paths member
          obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
          exact satisfied record (scanned.selected.subset present)
        have needed := SourceCurrentConjunctionRequiredClassPass.satisfied_required _ symbol terms selectedActive selectedSatisfied
        exact language.trans ⟨And.left, fun accepted => ⟨accepted, needed⟩⟩
      · intro g s r p h n enoughG enoughS enoughR enoughP enoughH enoughN
        have done := scanned.run g s p h n (Nat.le_trans scanLimit enoughG) (Nat.le_trans scanLimit enoughS)
          (Nat.le_trans scanLimit enoughP) (Nat.le_trans scanLimit enoughH) (Nat.le_trans scanLimit enoughN)
        have prepared := stable r h
          (Nat.le_trans (SourceCurrentSharedScanRequiredForecast.required_worker scanned.selected _ _ _ _) enoughR)
          (Nat.le_trans (SourceCurrentSharedScanRequiredForecast.required_reader scanned.selected _ _ _ _) enoughH)
        change SourceEqualityRequiredExecution.requireAll r h
          (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values middle.native.machine.heap = .done results heap at prepared
        simp only [SourceCurrentSharedScanRequiredWorker.prepare, SourceCurrentAllocatedSharedLocalWorker.scan, done,
          SourceCurrentAllocatedSharedLocalWorker.Outcome.bind, SourceCurrentAllocatedSharedLocalWorker.required, prepared]

end MicroCFTA.SourceCurrentSharedScanRequiredNumeric
