import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageCapacity

namespace MicroCFTA.FiniteOrdinaryPassStageCapacityChecks
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "PassCapacity" => SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity
local notation "StageCapacity" => SourceCurrentAllocatedFiniteOrdinaryStageCapacity.StageCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The plan selects the literal returned forest, full checked state, and memo from an earlier tail. -/
theorem exact_tail_plan (bits : Nat) {record records values results}
    {before after : Checked (bits + 2)} {memo saved : Memo}
    (capacity : PassCapacity bits (record :: records) values before memo)
    (actual : Fold records values before memo results after saved) :
    SourceCurrentAllocatedFiniteOrdinaryClassCapacity.ClassCapacity bits record results after saved :=
  capacity.head actual

section Initial
variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
include ready admitted available domain physical covered native merged valid

/-- The public finite pass propagates Empty without a numeric bound and keeps the entire state. -/
theorem empty_records_propagate :
    ∃ next final,
      PassReads formulas solver (Pass.done (Fold.nil (values := values) (before := before) (memo := memo))) memos final ∧
      Receipt formulas solver next [] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate values)
        before memo memos final ∧ NativeStored before.native ∧ MergeStored memo ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, afterNative, afterMerge, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryPassCapacity.finite bits formulas solver inventory
      (records := []) (SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity.nil)
      (by intro record member; cases member) (by intro record member; cases member)
      ready admitted available domain physical covered native merged memos valid
  cases actual with
  | done lower =>
      cases lower
      exact ⟨next, final, reads, receipt, afterNative, afterMerge, related⟩

/-- The constructed pass derives all positional bounds, admission, and global validity together. -/
theorem pass_same_return (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (capacity : PassCapacity bits records values before memo) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧ Ready after ∧ At formulas solver next after ∧
      Valid after.native.machine.heap final ∧ NativeStored after.native ∧ MergeStored saved ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Children results ∧
      MergedOrdinaryHeight.childrenHeight results ≤ MergedOrdinaryHeight.childrenHeight values := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, afterNative, afterMerge, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryPassCapacity.finite bits formulas solver inventory capacity coherent active
      ready admitted available domain physical covered native merged memos valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt.ready, receipt.admitted, receipt.globals.valid,
    afterNative, afterMerge, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain related,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height related⟩
end Initial

variable [DecidableEq (Value Symbol Guard)]

/-- No class is reached after an empty Scan, so no numeric query plan is needed. -/
theorem empty_stage_capacity (bits budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo) :
    StageCapacity bits budget [] values before fourth memo := by
  constructor
  intro selected middle savedFourth actual kept retained fuel readFuel requiredValues heap required
  cases retained
  exact .nil

/-- The stage plan retains the exact earlier required return before any class pass completes. -/
theorem exact_required_entry (bits budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (capacity : StageCapacity bits budget records values before fourth memo)
    {selected middle savedFourth}
    (scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth none selected middle savedFourth)
    (kept : List SourceEqualityClassOrder.Record) (retained : SourceCurrentConjunctionSelectedRecords.Retained scan records kept)
    (fuel readFuel : Nat) (requiredValues : List (Value Symbol Guard)) (heap : InternedConstructorTemplates.State Symbol Guard)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done requiredValues heap) :
    PassCapacity bits kept requiredValues (SourceCurrentConjunctionClassScan.advanceHeap middle heap) memo :=
  capacity.pass scan kept retained fuel readFuel requiredValues heap required

/-- Finite ordinary Scan cannot stop; the derived finite stage keeps its exact full receipt and structural caches. -/
theorem stage_constructed_none (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (capacity : StageCapacity bits budget records values before fourth memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after savedFourth saved next final,
      ∃ actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo none results after savedFourth saved,
        SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final ∧
        SourceCurrentConjunctionScanClassPass.Receipt formulas solver next records values results before after fourth savedFourth memo saved none final ∧
        NativeStored after.native ∧ MergeStored saved ∧ All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  obtain ⟨outcome, results, after, savedFourth, saved, next, final, actual, reads, receipt, structural⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryStageCapacity.finite bits formulas solver inventory budget records values before fourth memo ready admitted
      available domain proper fields correct physical covered native merged capacity memos valid
  have noStop : outcome = none := by
    cases actual with
    | stopped scan =>
        have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain).1
        cases impossible
    | completed => rfl
  subst outcome
  exact ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt, structural⟩
end MicroCFTA.FiniteOrdinaryPassStageCapacityChecks

#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.exact_tail_plan
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.exact_tail_plan
#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.empty_records_propagate
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.empty_records_propagate
#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.pass_same_return
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.pass_same_return
#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.empty_stage_capacity
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.empty_stage_capacity
#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.exact_required_entry
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.exact_required_entry
#print axioms MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.stage_constructed_none
#check @MicroCFTA.FiniteOrdinaryPassStageCapacityChecks.stage_constructed_none
