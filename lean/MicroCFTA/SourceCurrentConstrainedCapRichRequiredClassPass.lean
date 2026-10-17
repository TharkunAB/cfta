import MicroCFTA.SourceCurrentConstrainedCapRichRequiredSupport
import MicroCFTA.SourceCurrentConstrainedCapRichClassPassSupport
import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

/-!
# Actual Required and class passes retain the original cap and masks

The class pass starts at the literal Required return and global memo bundle.
Its record masks come from the original input through actual Required reads.
The composed physical and language receipt remains intact. These theorems
verify supplied executions. They do not assert general class completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichRequiredClassPass
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassPass (Pass PassReads)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Original local facts derive class-entry masks and retain all laws through the same supplied whole pass. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (depth : Nat) (records : List SourceEqualityClassOrder.Record)
    {selected : EqualityNormalize.Constraints} {originals values results : List (Value Symbol Guard)}
    {before after : Checked width} {heap : Heap} {memo saved : Memo} {memos current final : Memos}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before (advanceHeap before heap))
    (requiredReads : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
      originals values before.native.machine.heap heap memos current)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    {actual : Pass records values (advanceHeap before heap) memo results after saved}
    (reads : PassReads formulas solver actual current final)
    (ready : Ready before) (available : Values before.native.machine.heap originals) (closed : ClosedValues originals)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (preparedValid : EndpointMemoGateTrace.Valid heap current)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ originals, Cap depth value)
    (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) :
    ∃ next, SourceCurrentConjunctionRequiredClassPass.Receipt formulas solver next records selected originals values
        before (advanceHeap before heap) memo results after saved current final ∧
      NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) originals results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
  have prepared := SourceCurrentConstrainedCapRichRequiredSupport.requireAll Plain depth requiredReads
    ready available closed native merged bounded
  obtain ⟨expected, _expectedHeap, _kept, _resident, expectedClosed, expectedStable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete (SourceEqualitySelectedRequired.paths selected) originals
      before.native.machine.heap ready.semantic.ready available closed
  have same := SourceEqualityRequiredExecution.stable_unique expectedStable required.stable
  have preparedClosed : ClosedValues values := same.1 ▸ expectedClosed
  have preparedMasks := fun record member => SourceCurrentConstrainedCapForestSupport.record_masks
    prepared.2.2.1 record (supported record member)
  obtain ⟨_richInventory, _richReceipt, nativeAfter, mergeAfter, related, capsAfter, closedAfter⟩ :=
    SourceCurrentConstrainedCapRichClassPassSupport.pass formulas solver inventory depth reads coherent active
      required.ready required.admitted required.resident preparedClosed (physicalStored.grows required.effects.keeps)
      covered preparedValid prepared.1 prepared.2.1 prepared.2.2.2.1 preparedMasks
  obtain ⟨next, receipt⟩ := SourceCurrentConjunctionRequiredClassPass.verified formulas solver inventory required
    records selectedEq coherent active reads physicalStored covered preparedValid
  exact ⟨next, receipt, nativeAfter, mergeAfter,
    SourceCurrentConstrainedCapForestSupport.trans prepared.2.2.1 related, capsAfter, closedAfter⟩

end MicroCFTA.SourceCurrentConstrainedCapRichRequiredClassPass
