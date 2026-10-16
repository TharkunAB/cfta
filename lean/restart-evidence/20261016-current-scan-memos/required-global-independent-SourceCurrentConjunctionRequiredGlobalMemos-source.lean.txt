import MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos
import MicroCFTA.SourceCurrentConjunctionRequired
import MicroCFTA.SourceCurrentConjunctionSelectedRecords
import MicroCFTA.SourceCurrentRequiredQueryMemos

/-!
# Current checked Scan and required paths with the same global tables

A successful current Scan derives its literal final checked state.
Required execution starts at that returned heap and operation cache.
The stable worker bound derives its actual global unfolding receipts.
Final inventory laws, both native tables, domain cache, loaded fields,
and both global query tables retain their exact source relationships.
Later class edits and the constrained outer caller remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
variable {width : Nat}

/-- Actual successful checked Scan and selected paths derive finite required execution and every memo receipt. -/
theorem scan_required_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo none selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ scanMemos finalMemos next results heap,
      SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos scanMemos ∧
      SourceCurrentConjunctionRequired.Receipt formulas solver next selected values results after (advanceHeap after heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results after.native.machine.heap heap scanMemos finalMemos ∧
      Valid heap finalMemos ∧ Extends scanMemos.unfolding finalMemos.unfolding ∧
      finalMemos.query = scanMemos.query ∧
      Effects (physical before) (physical (advanceHeap after heap)) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨scanMemos, scanReads, scanValid, scanReady, _, scanValues, _, _⟩ :=
    SourceCurrentConjunctionClassScanGlobalMemos.scan_memos actual ready available proper formulas solver correct ranges memos valid
  obtain ⟨next, results, heap, receipt, effects, fourth, retained⟩ :=
    SourceCurrentConjunctionRequired.scan_required_complete formulas solver inventory actual ready admitted available
      proper active correct ranges
  obtain ⟨fuel, readFuel, enough⟩ := receipt.stable
  have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨finalMemos, requiredReads, finalValid, unfoldRetained, query⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results after.native.machine.heap heap done
      scanReady.semantic scanReady.costs scanValues scanMemos scanValid
  exact ⟨scanMemos, finalMemos, next, results, heap, scanReads, receipt, requiredReads, finalValid,
    unfoldRetained, query, effects, fourth, retained⟩

/-- Original records retain their actual selected positions through the same required execution. -/
theorem records_required_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    {budget : Nat} {values : List (Value Symbol Guard)} {selected : Constraints}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values (records.map SourceEqualityClassOrder.Record.paths)
      before memo none selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values
      (records.map SourceEqualityClassOrder.Record.paths) before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ kept scanMemos finalMemos next results heap,
      SourceCurrentConjunctionSelectedRecords.Retained actual records kept ∧ kept.Sublist records ∧
      kept.map SourceEqualityClassOrder.Record.paths = selected ∧
      (∀ record ∈ kept, SourceEqualityClassOrder.Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths) ∧
      SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos scanMemos ∧
      SourceCurrentConjunctionRequired.Receipt formulas solver next selected values results after (advanceHeap after heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results after.native.machine.heap heap scanMemos finalMemos ∧
      Valid heap finalMemos ∧ SourceCurrentEmptinessMemo.Correct formulas solver heap saved := by
  obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actual
  have selectedFields := retained.fields
  have originalProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have active : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  obtain ⟨scanMemos, finalMemos, next, results, heap, scanReads, receipt, requiredReads, finalValid, _, _, _, fourth, _⟩ :=
    scan_required_memos formulas solver inventory actual ready admitted available originalProper active correct ranges memos valid
  exact ⟨kept, scanMemos, finalMemos, next, results, heap, retained, selectedFields.1, selectedFields.2,
    (fun record member => fields record (selectedFields.1.subset member)), scanReads, receipt, requiredReads, finalValid, fourth⟩

end MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
