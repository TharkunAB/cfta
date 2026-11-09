import MicroCFTA.SourceCurrentSharedActualParentSemanticReads
import MicroCFTA.SourceCurrentSharedScanNativeStores
import MicroCFTA.SourceCurrentAllocatedSharedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedSharedRecordScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedLocalReductionActual

/-!
# Native stores at a resource-admitted Parent Scan

The numeric Parent receipt retains its actual ordered shared Scan reads.
Successful worker determinism identifies its full selected return.
The literal precheck retains the native state and supplies Ready.
Initial native stores then advance through that same admitted Scan.
-/
namespace MicroCFTA.SourceCurrentSharedActualParentScanNativeStores
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentSharedScanCallerNumeric (ScanReads)
open SourceCurrentNativeRequestPositivePositions (Support)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem preparation_scan
    {width budget : Nat} {records : List SourceEqualityClassOrder.Record} {values results : List Node}
    {before after : Checked width} {fourth saved : Fourth} {outcome : Option EqualityNormalize.Class}
    {kept : List SourceEqualityClassOrder.Record} {memos final : Memos}
    {execution : SourceCurrentSharedScanRequiredNumeric.Execution budget records values before fourth
      outcome kept results after saved}
    (reads : SourceCurrentSharedScanRequiredNumeric.Reads execution memos final) :
    ∃ selectedOutcome selected scanned scanFourth scanMemos scanFinal g s p h n,
      SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records before fourth =
        .done (selectedOutcome, selected) scanned scanFourth ∧
      ScanReads budget values records before fourth selectedOutcome selected scanned scanFourth scanMemos scanFinal := by
  cases reads with
  | @stopped before fourth paths kept after saved g s p h n memos final observed calls =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, observed, calls⟩
  | @prepared before fourth kept middle saved results heap g s p h n r read
      observed required memos scanMemos final first second =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, observed, first⟩

private theorem local_scan
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {width budget : Nat} {loaded : Allocated} {inherited : EqValue} {values results : List Node}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    (execution : SourceCurrentSharedLocalNumeric.Execution budget loaded inherited values
      before fourth memo results after savedFourth saved)
    (reads : SourceCurrentSharedLocalNumeric.Reads formulas solver execution memos final)
    {records : List SourceEqualityClassOrder.Record}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok (.classes records)) :
    ∃ outcome selected scanned scanFourth scanMemos scanFinal g s p h n,
      SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
        (prefixState before loaded inherited) fourth = .done (outcome, selected) scanned scanFourth ∧
      ScanReads budget values records (prefixState before loaded inherited) fourth
        outcome selected scanned scanFourth scanMemos scanFinal := by
  cases reads with
  | @unchanged before fourth memo actual memos =>
      have impossible := Except.ok.inj (actual.symm.trans precheck)
      cases impossible
  | @emptyChildren before fourth memo actual memos =>
      have impossible := Except.ok.inj (actual.symm.trans precheck)
      cases impossible
  | @classes before fourth memo originalRecords outcome results after
      savedFourth saved actual continuation memos final calls =>
      have same := Except.ok.inj (actual.symm.trans precheck)
      cases same
      cases calls with
      | stopped calls => exact preparation_scan calls
      | completed calls last => exact preparation_scan calls

/-- Initial resources derive admission and the native stores at the same selected Scan return. -/
theorem selected_scan
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List Node) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : SourceCurrentSharedParentNumeric.LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentSharedParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedSharedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records kept : List SourceEqualityClassOrder.Record} {scanned : Checked (bits + 2)} {scanFourth : Fourth}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.checked.operations).1 =
      .ok (.classes records))
    (scanCall : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
      (prefixState before.checked loaded inherited) before.fourth = .done (none, kept) scanned scanFourth)
    (current : Current before.checked)
    (supported : Support before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap) :
    ∃ next final,
      SourceCurrentSharedParentNumeric.Receipt formulas solver next profile budget symbol original loaded inherited values
        before memos result after savedFourth saved final ∧
      ∃ scanMemos scanFinal,
      ScanReads budget values records (prefixState before.checked loaded inherited) before.fourth
        none kept scanned scanFourth scanMemos scanFinal ∧
      Ready scanned ∧
      SourceCurrentConjunctionRowsAllocation.Effects
        (physical (prefixState before.checked loaded inherited)) (physical scanned) ∧
      SourceRecursiveIntersectionKernel.Extension
        (prefixState before.checked loaded inherited).native.machine scanned.native.machine ∧
      Values scanned.native.machine.heap values ∧ Current scanned ∧
      Support scanned.native.machine.heap scanned.native ∧ Nonempty (History empty scanned.native.machine.heap)
 := by
  obtain ⟨next, final, numeric⟩ := SourceCurrentSharedActualParentSemanticReads.parent formulas solver inventory budget
    symbol original loaded inherited values before memos initial frame profile fits live reserved observed
  have cut : ∃ outcome selected scanState returnedFourth scanMemos scanFinal G S P H N,
      SourceCurrentAllocatedSharedRecordScanWorker.scan G S P H N budget values records
        (prefixState before.checked loaded inherited) before.fourth =
          .done (outcome, selected) scanState returnedFourth ∧
      ScanReads budget values records (prefixState before.checked loaded inherited) before.fourth
        outcome selected scanState returnedFourth scanMemos scanFinal := by
    cases numeric.reads with
    | rejected test =>
        rw [noncontradictory] at test
        cases test
    | live _ lower built =>
        exact local_scan lower.actual lower.reads precheck
  obtain ⟨outcome, selected, scanState, returnedFourth, scanMemos, scanFinal,
    G, S, P, H, N, completed, actualScan⟩ := cut
  obtain ⟨sameResult, sameState, sameFourth⟩ :=
    SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique completed scanCall
  obtain ⟨sameOutcome, sameSelected⟩ := Prod.mk.inj sameResult
  subst outcome selected scanState returnedFourth
  obtain ⟨cached, found, inheritedReady, available⟩ := live noncontradictory
  obtain ⟨own, prefixReceipt⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
  have proper := (prefixReceipt.classes records rfl).1
  have properRecords : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
    intro record member path included
    exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩) path included
  have prefixCurrent : Current (prefixState before.checked loaded inherited) := by
    simpa only [SourceCurrentConstrainedCapCurrentNative.At, SourceCurrentAllocatedPrecheck.state_native] using current
  have prefixSupport : Support (prefixState before.checked loaded inherited).native.machine.heap
      (prefixState before.checked loaded inherited).native := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using supported
  have prefixHistory : History empty (prefixState before.checked loaded inherited).native.machine.heap := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using causal
  have prefixAvailable : Values (prefixState before.checked loaded inherited).native.machine.heap values := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using available
  exact ⟨next, final, numeric, scanMemos, scanFinal, actualScan,
    SourceCurrentSharedScanNativeStores.scan formulas solver actualScan prefixReceipt.ready prefixAvailable properRecords
      prefixCurrent prefixSupport prefixHistory⟩

end MicroCFTA.SourceCurrentSharedActualParentScanNativeStores
