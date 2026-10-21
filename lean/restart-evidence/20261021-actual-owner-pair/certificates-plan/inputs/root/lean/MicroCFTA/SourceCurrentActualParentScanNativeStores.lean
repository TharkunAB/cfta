import MicroCFTA.SourceCurrentActualParentSemanticReads
import MicroCFTA.SourceCurrentScanNativeStores
import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedLocalReductionActual

/-!
# Native stores at a resource-admitted Parent Scan

The numeric Parent receipt contains the actual checked Scan graph.
Successful worker determinism identifies its full selected return.
The literal precheck retains the native state and supplies Ready.
Initial native stores then advance through that same admitted Scan.
-/
namespace MicroCFTA.SourceCurrentActualParentScanNativeStores
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Scan Ready)
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

private theorem graph_scan {width budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated}
    {inherited : EqValue} {values : List Node} {before after : Checked width} {fourth savedFourth : Fourth}
    {memo saved : Memo} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values
      before fourth memo result after savedFourth saved)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records : List SourceEqualityClassOrder.Record}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok (.classes records)) :
    ∃ outcome selected scanned scanFourth,
      Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
        values (records.map SourceEqualityClassOrder.Record.paths)
        (prefixState before loaded inherited) fourth outcome selected scanned scanFourth := by
  cases actual with
  | rejected test =>
      rw [noncontradictory] at test
      cases test
  | live _ reduction _ =>
      cases reduction with
      | unchanged actual =>
          have impossible := Except.ok.inj (actual.symm.trans precheck)
          cases impossible
      | emptyChildren actual =>
          have impossible := Except.ok.inj (actual.symm.trans precheck)
          cases impossible
      | classes actual continuation =>
          have same := Except.ok.inj (actual.symm.trans precheck)
          cases same
          cases continuation with
          | stopped scan => exact ⟨_, _, _, _, scan⟩
          | completed scan _ _ _ => exact ⟨_, _, _, _, scan⟩

/-- Initial resources derive admission and the native stores at the same selected Scan return. -/
theorem selected_scan
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List Node) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : SourceCurrentParentNumeric.LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records kept : List SourceEqualityClassOrder.Record} {scanned : Checked (bits + 2)} {scanFourth : Fourth}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.checked.operations).1 =
      .ok (.classes records))
    (scanCall : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (prefixState before.checked loaded inherited) before.fourth = .done (none, kept) scanned scanFourth)
    (current : Current before.checked)
    (supported : Support before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap) :
    ∃ next final,
      SourceCurrentParentNumeric.Receipt formulas solver next profile budget symbol original loaded inherited values
        before memos result after savedFourth saved final ∧
      Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
        values (records.map SourceEqualityClassOrder.Record.paths)
        (prefixState before.checked loaded inherited) before.fourth none
        (kept.map SourceEqualityClassOrder.Record.paths) scanned scanFourth ∧
      Ready scanned ∧
      SourceCurrentConjunctionRowsAllocation.Effects
        (physical (prefixState before.checked loaded inherited)) (physical scanned) ∧
      SourceRecursiveIntersectionKernel.Extension
        (prefixState before.checked loaded inherited).native.machine scanned.native.machine ∧
      Values scanned.native.machine.heap values ∧ Current scanned ∧
      Support scanned.native.machine.heap scanned.native ∧ Nonempty (History empty scanned.native.machine.heap)
 := by
  obtain ⟨next, final, numeric⟩ := SourceCurrentActualParentSemanticReads.parent formulas solver inventory budget
    symbol original loaded inherited values before memos initial frame profile fits live reserved observed
  obtain ⟨outcome, selected, scanState, returnedFourth, actualScan⟩ :=
    graph_scan numeric.actual noncontradictory precheck
  obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete actualScan
  have completed := stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)
  have mapped := SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records
    (prefixState before.checked loaded inherited) before.fourth
  rw [scanCall] at mapped
  have literal : SourceCurrentAllocatedScanWorker.scan g s p h n budget values
      (records.map SourceEqualityClassOrder.Record.paths) (prefixState before.checked loaded inherited)
      before.fourth = .done (none, kept.map SourceEqualityClassOrder.Record.paths) scanned scanFourth := by
    simpa only [SourceCurrentAllocatedRecordScanWorker.mapPaths] using mapped.symm
  obtain ⟨sameResult, sameState, sameFourth⟩ :=
    SourceCurrentAllocatedScanWorkerStability.scan_done_unique completed literal
  obtain ⟨sameOutcome, sameSelected⟩ := Prod.mk.inj sameResult
  subst outcome selected scanState returnedFourth
  obtain ⟨cached, found, inheritedReady, available⟩ := live noncontradictory
  obtain ⟨own, prefixReceipt⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
  have proper := (prefixReceipt.classes records rfl).1
  have prefixCurrent : Current (prefixState before.checked loaded inherited) := by
    simpa only [SourceCurrentConstrainedCapCurrentNative.At, SourceCurrentAllocatedPrecheck.state_native] using current
  have prefixSupport : Support (prefixState before.checked loaded inherited).native.machine.heap
      (prefixState before.checked loaded inherited).native := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using supported
  have prefixHistory : History empty (prefixState before.checked loaded inherited).native.machine.heap := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using causal
  have prefixAvailable : Values (prefixState before.checked loaded inherited).native.machine.heap values := by
    simpa only [SourceCurrentAllocatedPrecheck.state_native] using available
  exact ⟨next, final, numeric, actualScan,
    SourceCurrentScanNativeStores.scan formulas solver actualScan prefixReceipt.ready prefixAvailable proper
      prefixCurrent prefixSupport prefixHistory⟩

end MicroCFTA.SourceCurrentActualParentScanNativeStores
