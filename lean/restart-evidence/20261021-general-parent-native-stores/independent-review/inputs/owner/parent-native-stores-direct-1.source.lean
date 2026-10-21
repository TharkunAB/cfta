import MicroCFTA.SourceCurrentActualParentSemanticReads
import MicroCFTA.SourceCurrentActualParentSelectedCertificates
import MicroCFTA.SourceCurrentRequiredPositiveChronology
import MicroCFTA.SourceCurrentNativePositiveSupportAdvance
import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion

/-!
# Native stores at every completed Parent return

One actual numeric receipt fixes every local read and returned state.
The same Scan and Required cuts supply their current stores and history.
Both constructor outcomes retain their actual physical node records.
-/
namespace MicroCFTA.SourceCurrentActualParentNativeStores
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Scan Ready)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentNativeRequestPositivePositions (Support)
open SourceCurrentNativeMuPublication (History)
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
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
local notation "Normal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem constructed
    {width : Nat} (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (loaded : Allocated) (children : List Node) (before : Checked width)
    {result : EdgeValue Symbol Guard} {after : Checked width}
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints loaded.stored)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.operations
      (SourceEqualityConjoinAllocation.readback loaded))
    (available : Values before.native.machine.heap children)
    (current : Current before) (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap)
    (built : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after)) :
    Support after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) := by
  obtain ⟨chosen, returned, receipt⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory
    symbol loaded children before ready admitted storedReady field available
  have same := Prod.mk.inj (receipt.actual.symm.trans built)
  have valueSame := Except.ok.inj same.1
  cases valueSame
  cases same.2
  have finalSupport := SourceCurrentNativePositiveSupportAdvance.advance before after current supported
    receipt.ready.good receipt.extension receipt.nodes receipt.edges
  have sourceBuild := (SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard children
    before.operations before.native.machine.heap ready.good.operations storedReady).1
  have records : after.native.machine.heap.nodeRecords = before.native.machine.heap.nodeRecords := by
    have identity : (SourceCurrentAllocatedMkEdge.build symbol loaded children before).2.native.machine.heap.nodeRecords =
        before.native.machine.heap.nodeRecords := by
      change (SourceEqualityMkEdgeAllocation.build symbol loaded.stored loaded.guard children
        before.operations before.native.machine.heap).2.2.nodeRecords = _
      rw [sourceBuild]
      cases SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length <;> rfl
    simpa only [built] using identity
  have interval : History before.native.machine.heap after.native.machine.heap :=
    .retain _ _ (fun key entry body depth ordinary present => by rw [records] at present; exact present)
  exact ⟨finalSupport, ⟨.trans causal interval⟩⟩

private theorem classes
    {width budget : Nat} (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {records : List SourceEqualityClassOrder.Record} {values results : List Node}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo}
    {outcome : Option EqualityNormalize.Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo
      outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ EqualityNormalize.Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (normal : Normal before.native.machine.heap) (current : Current before)
    (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) (merged : MergeStored memo) (positive : MergeSupport memo) :
    ∃ next, Ready after ∧ At formulas solver next after ∧ Effects (physical before) (physical after) ∧
      Values after.native.machine.heap results ∧ Current after ∧ Support after.native.machine.heap after.native ∧
      Nonempty (History empty after.native.machine.heap) ∧ MergeStored saved ∧ MergeSupport saved := by
  have active : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, EqualityNormalize.Nontrivial paths := by
    intro paths member
    obtain ⟨record, included, rfl⟩ := List.mem_map.mp member
    exact (fields record included).2.2
  cases reads with
  | stopped first =>
      rename_i paths selected scan
      obtain ⟨finalReady, effects, extension, _values, finalCurrent, finalSupport, finalHistory⟩ :=
        SourceCurrentScanNativeStores.scan formulas solver scan ready available proper current supported causal
      obtain ⟨next, _ready, finalAdmission, _effects, _originals, _correct, _retained, _sound⟩ :=
        SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory scan ready admitted available
          proper active correct ranges
      exact ⟨next, finalReady, finalAdmission, effects,
        (SourceEqualityEmptyPropagation.erased_scope _ values).1, finalCurrent, finalSupport, finalHistory, merged, positive⟩
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      obtain ⟨scanReady, scanEffects, _extension, scanValues, scanCurrent, scanSupport, ⟨scanHistory⟩⟩ :=
        SourceCurrentScanNativeStores.scan formulas solver scan ready available proper current supported causal
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available proper
        formulas solver correct ranges valid).1
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available proper active correct ranges required
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second scanReady.semantic
        scanReady.costs scanValues scanValid).1
      have gates := SourceCurrentConjunctionRequired.selected_primary formulas solver inventory scan ready admitted
        available proper active correct ranges
      obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete scan
      have scanDone := stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _)
      have scanNormal := SourceCurrentUnionNormalScan.scan G S P H N budget values
        (records.map SourceEqualityClassOrder.Record.paths) before fourth normal
      rw [scanDone] at scanNormal
      obtain ⟨keptSublist, selectedEq⟩ := retained.fields
      obtain ⟨next, receipt, finalCurrent, finalMerged, _corridors, finalSupport, finalHistory,
          finalPositive, _back⟩ :=
        SourceCurrentRequiredPositiveChronology.pass formulas solver requiredInventory requiredReceipt
          scanReady.semantic scanNormal scanReady.costs scanValues gates scanCurrent scanSupport scanHistory
          kept selectedEq (fun record member => (fields record (keptSublist.subset member)).1)
          (fun record member => (fields record (keptSublist.subset member)).2.2) last
          (physicalStored.grows scanEffects.keeps) covered requiredValid merged positive
      exact ⟨next, receipt.ready, receipt.admitted,
        scanEffects.trans (requiredReceipt.effects.trans receipt.effects), receipt.available,
        finalCurrent, finalSupport, finalHistory, finalMerged, finalPositive⟩

/-- Every literal completed Parent return retains its same receipt and current native stores. -/
theorem parent
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : SourceCurrentParentNumeric.LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      before.checked.native.machine.heap before.checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support before.merge)
    {g s r e p h m c n : Nat} {result : EdgeValue Symbol Guard} {after : Checked (bits + 2)}
    {savedFourth : Fourth} {saved : Memo}
    (observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited values
      before.checked before.fourth before.merge = .done result after savedFourth saved) :
    ∃ next final, SourceCurrentParentNumeric.Receipt formulas solver next profile budget symbol original loaded
      inherited values before memos result after savedFourth saved final ∧
      SourceCurrentNativeRequestPositivePositions.Support after.native.machine.heap after.native ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty after.native.machine.heap) ∧
      SourceCurrentConstrainedCapMemoMerge.Stored
        (fun guard : Guard => SourceMemoGate.plain guard = true) saved ∧
      SourceCurrentMergePositivePosition.Support saved := by
  obtain ⟨next, final, numeric⟩ := SourceCurrentActualParentSemanticReads.parent formulas solver inventory budget
    symbol original loaded inherited values before memos initial frame profile fits live reserved observed
  refine ⟨next, final, numeric, ?_⟩
  have current := SourceCurrentConstrainedCapOperandFrame.current frame
  cases numeric.reads with
  | rejected =>
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory symbol before.checked
        initial.ready initial.admitted
      have finalSupport := SourceCurrentNativePositiveSupportAdvance.advance before.checked _ current supported
        constructor.ready.good constructor.extension constructor.nodes constructor.edges
      have records : (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2.native.machine.heap.nodeRecords =
          before.checked.native.machine.heap.nodeRecords := rfl
      have interval : History before.checked.native.machine.heap
          (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2.native.machine.heap :=
        .retain _ _ (fun key entry body depth ordinary present => by rw [records] at present; exact present)
      exact ⟨finalSupport, ⟨.trans causal interval⟩, merged, positiveMemo⟩
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available⟩ := live test
      have localStores : ∃ localInventory, Ready middle ∧ At formulas solver localInventory middle ∧
          Effects (physical before.checked) (physical middle) ∧ Values middle.native.machine.heap children ∧
          Current middle ∧ Support middle.native.machine.heap middle.native ∧
          Nonempty (History empty middle.native.machine.heap) ∧ MergeStored saved ∧ MergeSupport saved := by
        cases reads with
        | unchanged =>
            rename_i precheck
            obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
              before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
            have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
              ⟨checked.ready, checked.admitted, frame.context, frame.joint, frame.origins⟩
            exact ⟨inventory, checked.ready, checked.admitted, checked.effects, available,
              SourceCurrentConstrainedCapOperandFrame.current prefixFrame, supported, ⟨causal⟩, merged, positiveMemo⟩
        | emptyChildren =>
            rename_i precheck
            obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
              before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
            have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
              ⟨checked.ready, checked.admitted, frame.context, frame.joint, frame.origins⟩
            exact ⟨inventory, checked.ready, checked.admitted, checked.effects,
              (SourceEqualityEmptyPropagation.erased_scope _ values).1,
              SourceCurrentConstrainedCapOperandFrame.current prefixFrame, supported, ⟨causal⟩, merged, positiveMemo⟩
        | classes classReads =>
            rename_i records outcome precheck continuation
            obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
              before.checked original loaded inherited initial.ready initial.admitted cached found inheritedReady precheck
            obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
            have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
              ⟨checked.ready, checked.admitted, frame.context, frame.joint, frame.origins⟩
            have prefixFits : Fits profile (prefixState before.checked loaded inherited) :=
              ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩
            have classRoom : SourceCurrentClassesForecast.Reserved bits budget values.length records
                (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) profile := by
              simpa only [SourceCurrentParentForecast.Reserved, test, Bool.false_eq_true, ↓reduceIte,
                SourceCurrentLocalForecast.Reserved, precheck] using reserved
            obtain ⟨_, _, _, _, _, boundedScan⟩ := SourceCurrentScanNumeric.complete formulas solver
              (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) budget values
              (records.map SourceEqualityClassOrder.Record.paths) (prefixState before.checked loaded inherited) before.fourth
              inventory prefixFrame profile prefixFits available initial.correct
              (SourceCurrentConjunctionGuardUniverse.initial _ prefixFrame.ready.semantic.ready.semantic.1.normal.facts)
              proper classRoom.1 memos initial.globals
            obtain ⟨localInventory, finalReady, admitted, effects, finalValues, finalCurrent, finalSupport,
                finalHistory, finalMerged, finalPositive⟩ :=
              classes formulas solver inventory classReads checked.ready checked.admitted available proper fields
                initial.correct initial.stored initial.covered boundedScan.ranges initial.globals normal
                (SourceCurrentConstrainedCapOperandFrame.current prefixFrame) supported causal merged positiveMemo
            exact ⟨localInventory, finalReady, admitted, checked.effects.trans effects, finalValues, finalCurrent,
              finalSupport, finalHistory, finalMerged, finalPositive⟩
      obtain ⟨localInventory, ready, admitted, effects, childValues, localCurrent, localSupport,
          ⟨localHistory⟩, localMerged, localPositive⟩ := localStores
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.checked.operations.constraints
        initial.ready.good.operations.constraints cached loaded found
      have storedReady := loadedReady.1.grows effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations
          (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations original from
          ⟨cached, loaded, found⟩).grows effects.grows
      obtain ⟨finalSupport, finalHistory⟩ := constructed formulas solver localInventory symbol loaded children middle
        ready admitted storedReady field childValues localCurrent localSupport localHistory built
      exact ⟨finalSupport, finalHistory, localMerged, localPositive⟩

end MicroCFTA.SourceCurrentActualParentNativeStores
