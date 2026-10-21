import MicroCFTA.SourceCurrentActualParentScanNativeStores
import MicroCFTA.SourceCurrentConjunctionRequiredActual
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability
import MicroCFTA.SourceCurrentAllocatedRequiredReadValidity
import MicroCFTA.SourceCurrentScanNumeric
import MicroCFTA.SourceCurrentUnionNormalScan
import MicroCFTA.SourceCurrentActualParentSemanticReads
import MicroCFTA.SourceCurrentScanNativeStores
import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedLocalReductionActual
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame


/-!
# Selected certificates from one resource-admitted Parent

The same historical read graph supplies the complete retained records.
Successful worker uniqueness identifies the actual Required and Pass cuts.
Initial numeric resources derive the older Scan range interface internally.
-/
namespace MicroCFTA.SourceCurrentActualParentSelectedCertificates
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


private theorem selected_graph
    {width budget : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List Node} {before after : Checked width} {fourth savedFourth : Fourth}
    {memo saved : Memo} {result : EdgeValue Symbol Guard} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values
      before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (noncontradictory : SourceEqualityMkEdgeAllocation.contradictory original = false)
    {records kept : List SourceEqualityClassOrder.Record} {scanned : Checked width} {scanFourth : Fourth}
    (precheck : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
      .ok (.classes records)) {g s r e p h m c n : Nat}
    (scanCall : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (prefixState before loaded inherited) fourth = .done (none, kept) scanned scanFourth)
    {preparedValues : List Node} {preparedHeap : InternedConstructorTemplates.State Symbol Guard}
    {classAfter : Checked width}
    (requiredCall : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
      scanned.native.machine.heap = .done preparedValues preparedHeap)
    (passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept preparedValues
      (SourceCurrentConjunctionClassScan.advanceHeap scanned preparedHeap) memo =
      .done result.children classAfter saved) :
    ∃ scanMemos preparedMemos,
      ∃ trace : Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
        values (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth none
        (kept.map SourceEqualityClassOrder.Record.paths) scanned scanFourth,
      ∃ retained : SourceCurrentConjunctionSelectedRecords.Retained trace records kept,
      ∃ pass : SourceCurrentAllocatedClassPass.Pass kept preparedValues
        (SourceCurrentConjunctionClassScan.advanceHeap scanned preparedHeap) memo result.children classAfter saved,
      (∃ built : SourceCurrentAllocatedMkEdge.build symbol loaded result.children classAfter = (.ok result, after),
        actual = SourceCurrentAllocatedParentEdge.Edge.live noncontradictory
          (SourceCurrentAllocatedLocalReduction.Reduction.classes precheck
            (SourceCurrentConjunctionScanClassPass.Reduction.completed trace retained requiredCall pass)) built) ∧
      SourceCurrentAllocatedScanSourceReads.ScanReads trace memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values preparedValues
        scanned.native.machine.heap preparedHeap scanMemos preparedMemos ∧
      SourceCurrentAllocatedClassPass.PassReads formulas solver pass preparedMemos final := by
  cases reads with
  | rejected =>
      rename_i test
      rw [noncontradictory] at test
      cases test
  | live localReads =>
      rename_i children middle test built reduction
      cases localReads with
      | unchanged =>
          rename_i checked
          have impossible := Except.ok.inj (checked.symm.trans precheck)
          cases impossible
      | emptyChildren =>
          rename_i checked
          have impossible := Except.ok.inj (checked.symm.trans precheck)
          cases impossible
      | classes classReads =>
          rename_i originalRecords outcome checked continuation
          have sameRecords := Except.ok.inj (checked.symm.trans precheck)
          cases sameRecords
          cases classReads with
          | stopped first =>
              rename_i paths selected scan
              obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete scan
              have completed := stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
                (Nat.le_refl _) (Nat.le_refl _)
              have mapped := SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records
                (prefixState before loaded inherited) fourth
              rw [scanCall] at mapped
              have literal : SourceCurrentAllocatedScanWorker.scan g s p h n budget values
                  (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth =
                  .done (none, kept.map SourceEqualityClassOrder.Record.paths) scanned scanFourth := by
                simpa only [SourceCurrentAllocatedRecordScanWorker.mapPaths] using mapped.symm
              have impossible := (Prod.mk.inj
                (SourceCurrentAllocatedScanWorkerStability.scan_done_unique completed literal).1).1
              cases impossible
          | completed first second last =>
              rename_i actualKept requiredValues actualScanned selected heap fuel readFuel
                actualScanMemos actualRequiredMemos required scan retained pass
              obtain ⟨G, S, P, H, N, stable⟩ :=
                SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
              have completed := stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
                (Nat.le_refl _) (Nat.le_refl _)
              obtain ⟨sameResult, sameState, sameFourth⟩ :=
                SourceCurrentAllocatedRecordScanWorkerStability.scan_done_unique completed scanCall
              have sameKept := (Prod.mk.inj sameResult).2
              cases sameKept
              cases sameState
              cases sameFourth
              have sameSelected := retained.fields.2
              cases sameSelected
              obtain ⟨sameRequired, sameHeap⟩ :=
                SourceCurrentConjunctionRequiredActual.required_unique required requiredCall
              cases sameRequired
              cases sameHeap
              obtain ⟨E, P, H, M, C, N, stablePass⟩ :=
                SourceCurrentAllocatedClassWorkerCompletion.pass_complete pass
              have passDone := stablePass E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
                (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
              obtain ⟨sameChildren, sameClassState, _⟩ :=
                SourceCurrentAllocatedClassWorkerStability.pass_done_unique passDone passCall
              cases sameChildren
              cases sameClassState
              exact ⟨actualScanMemos, actualRequiredMemos, scan, retained, pass, ⟨built, rfl⟩, first, second, last⟩

/-- Initial Parent resources derive the certificates at the same actual selected cuts. -/
theorem selected_certificates
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
    {preparedValues : List Node} {preparedHeap : InternedConstructorTemplates.State Symbol Guard}
    {classAfter : Checked (bits + 2)}
    (requiredCall : SourceEqualityRequiredExecution.requireAll r h
      (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values
      scanned.native.machine.heap = .done preparedValues preparedHeap)
    (passCall : SourceCurrentAllocatedClassWorker.pass e p h m c n kept preparedValues
      (SourceCurrentConjunctionClassScan.advanceHeap scanned preparedHeap) before.merge =
      .done result.children classAfter saved)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
    (supported : Support before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap) :
    ∃ next final own preparedInventory scanMemos preparedMemos,
      ∃ numeric : SourceCurrentParentNumeric.Receipt formulas solver next profile budget symbol original loaded inherited values
        before memos result after savedFourth saved final,
      ∃ trace : Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
        values (records.map SourceEqualityClassOrder.Record.paths)
        (prefixState before.checked loaded inherited) before.fourth none
        (kept.map SourceEqualityClassOrder.Record.paths) scanned scanFourth,
      ∃ retained : SourceCurrentConjunctionSelectedRecords.Retained trace records kept,
      ∃ pass : SourceCurrentAllocatedClassPass.Pass kept preparedValues
        (SourceCurrentConjunctionClassScan.advanceHeap scanned preparedHeap) before.merge result.children classAfter saved,
      (∃ built : SourceCurrentAllocatedMkEdge.build symbol loaded result.children classAfter = (.ok result, after),
        numeric.actual = SourceCurrentAllocatedParentEdge.Edge.live noncontradictory
          (SourceCurrentAllocatedLocalReduction.Reduction.classes precheck
            (SourceCurrentConjunctionScanClassPass.Reduction.completed trace retained requiredCall pass)) built) ∧
      SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before.checked own (.classes records) ∧
      SourceCurrentAllocatedScanSourceReads.ScanReads trace memos scanMemos ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) values preparedValues
        scanned.native.machine.heap preparedHeap scanMemos preparedMemos ∧
      SourceCurrentAllocatedClassPass.PassReads formulas solver pass preparedMemos final ∧
      SourceCurrentConjunctionRequired.Receipt formulas solver preparedInventory
        (kept.map SourceEqualityClassOrder.Record.paths) values preparedValues scanned
        (SourceCurrentConjunctionClassScan.advanceHeap scanned preparedHeap) ∧
      EndpointMemoGateTrace.Valid preparedHeap preparedMemos ∧
      Ready scanned ∧
      SourceCurrentConjunctionRowsAllocation.Effects
        (physical (prefixState before.checked loaded inherited)) (physical scanned) ∧
      SourceRecursiveIntersectionKernel.Extension
        (prefixState before.checked loaded inherited).native.machine scanned.native.machine ∧
      Values scanned.native.machine.heap values ∧ Current scanned ∧
      Support scanned.native.machine.heap scanned.native ∧ Nonempty (History empty scanned.native.machine.heap) ∧
      SourceCurrentRequiredUnionNormal.UnionNormal scanned.native.machine.heap := by
  have current : Current before.checked := SourceCurrentConstrainedCapOperandFrame.current frame
  obtain ⟨next, final, numeric, _selectedScan, scanReady, effects, extension, scanAvailable,
      scanCurrent, scanSupport, scanHistory⟩ :=
    SourceCurrentActualParentScanNativeStores.selected_scan formulas solver inventory budget symbol original loaded
      inherited values before memos initial frame profile fits live reserved observed noncontradictory precheck
      scanCall current supported causal
  obtain ⟨scanMemos, preparedMemos, trace, retained, pass, assembled, first, second, last⟩ :=
    selected_graph numeric.reads noncontradictory precheck scanCall requiredCall passCall
  obtain ⟨cached, found, inheritedReady, available⟩ := live noncontradictory
  obtain ⟨own, prefixReceipt⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
  obtain ⟨proper, _, _, _, _, fields⟩ := prefixReceipt.classes records rfl
  have active : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, EqualityNormalize.Nontrivial paths := by
    intro paths member
    obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
    exact (fields record included).2.2
  have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
    ⟨prefixReceipt.ready, prefixReceipt.admitted, frame.context, frame.joint, frame.origins⟩
  have prefixFits : Fits profile (prefixState before.checked loaded inherited) :=
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩
  have classRoom : SourceCurrentClassesForecast.Reserved bits budget values.length records
      (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) profile := by
    simpa only [SourceCurrentParentForecast.Reserved, noncontradictory, Bool.false_eq_true, ↓reduceIte,
      SourceCurrentLocalForecast.Reserved, precheck] using reserved
  obtain ⟨_, _, _, _, _, boundedScan⟩ := SourceCurrentScanNumeric.complete formulas solver
    (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget values
    (records.map SourceEqualityClassOrder.Record.paths) (prefixState before.checked loaded inherited) before.fourth
    inventory prefixFrame profile prefixFits available initial.correct
    (SourceCurrentConjunctionGuardUniverse.initial _ prefixFrame.ready.semantic.ready.semantic.1.normal.facts)
    proper classRoom.1 memos initial.globals
  have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first prefixReceipt.ready available proper
    formulas solver initial.correct boundedScan.ranges initial.globals).1
  obtain ⟨preparedInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified formulas solver
    inventory trace prefixReceipt.ready prefixReceipt.admitted available proper active initial.correct
    boundedScan.ranges requiredCall
  have preparedValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
    scanReady.costs scanAvailable scanValid).1
  have scanNormal := SourceCurrentUnionNormalScan.records g s p h n budget values records
    (prefixState before.checked loaded inherited) before.fourth normal
  rw [scanCall] at scanNormal
  exact ⟨next, final, own, preparedInventory, scanMemos, preparedMemos, numeric, trace, retained, pass,
    assembled, prefixReceipt, first, second, last, requiredReceipt, preparedValid, scanReady, effects, extension,
    scanAvailable, scanCurrent, scanSupport, scanHistory, scanNormal⟩

end MicroCFTA.SourceCurrentActualParentSelectedCertificates
