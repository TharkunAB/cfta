import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScan
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
import MicroCFTA.SourceCurrentConjunctionScanClassPassActual

/-!
# Finite ordinary structure through the actual local class continuation

The primary Scan retains the same checked state and selects every class.
Actual required-path execution narrows each original child position.
The actual class pass receives that returned forest and warm tables.
No future domain, readiness, or completed-body premise is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStage
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentConjunctionScanClassPass (Reduction)
open SourceCurrentConjunctionScanClassPassActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Supplied actual stage reads derive both warm certificates and positional input bounds. -/
theorem structure_from_reads
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget sourceGate sourceReaches values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  cases reads with
  | stopped scanRead =>
      rename_i paths selected scan
      have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain).1
      cases impossible
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      have unchanged := SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain
      have sameMiddle := unchanged.2.2.1
      cases sameMiddle
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second ready.semantic
        ready.costs available (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper
          formulas solver correct ranges valid).1).1
      have narrowed := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap
        required ready.semantic available domain
      have nativeAfter : NativeStored (advanceHeap before heap).native :=
        SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored before.native _ nativeStored
      have retainedFields := retained.fields
      obtain ⟨_, _, native, merged, bounds⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.pass
        formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident narrowed.2.2.2.1
        (physicalStored.grows requiredReceipt.effects.keeps) covered nativeAfter mergeStored requiredValid
      exact ⟨native, merged, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans narrowed.2.2.2.2 bounds⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStage
