import MicroCFTA.SourceCurrentConstrainedCapRichClassSupport
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# All original masks through the actual class right fold

Each head class captures its actual tail result. Ordered all-path transport
derives its masks from the initial forest, including overlapping classes.
The same returned warm native and Merge tables retain their causal laws.
Final source empty propagation preserves the original cap and all masks.
These results verify supplied reads. General finite execution remains open.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichClassPassSupport
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem fold_support (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap depth value)
    (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) values) :
    NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
  induction reads generalizing inventory with
  | nil => exact ⟨native, merged, SourceCurrentConstrainedCapEditSupport.forest_refl Plain values, bounded, closed⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailMasks := fun own member => supported own (List.mem_cons_of_mem record member)
      have retained := ih inventory tailCoherent tailActive ready admitted available closed
        physicalStored covered valid native merged bounded tailMasks
      have domains : ∀ own ∈ records, ∀ path ∈ own.paths, ForestClosed (path.map Int.ofNat) values :=
        fun _ _ path _ => SourceCurrentConstrainedCapForestSupport.closed_domains values before.native.machine.heap
          ready.semantic available closed (path.map Int.ofNat)
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first
        tailCoherent tailActive ready admitted available domains physicalStored covered valid
      have headMasks := SourceCurrentConstrainedCapForestSupport.record_masks retained.2.2.1 record
        (supported record List.mem_cons_self)
      obtain ⟨_lastInventory, _lastReceipt, nativeAfter, mergeAfter, relatedAfter, capsAfter, closedAfter⟩ :=
        SourceCurrentConstrainedCapRichClassSupport.verified formulas solver next record depth
          (coherent record List.mem_cons_self) (active record List.mem_cons_self) last
          receipt.ready receipt.admitted receipt.available retained.2.2.2.2 receipt.stored receipt.covered
          receipt.globals.valid retained.1 retained.2.1 retained.2.2.2.1 headMasks
      exact ⟨nativeAfter, mergeAfter, SourceCurrentConstrainedCapForestSupport.trans retained.2.2.1 relatedAfter,
        capsAfter, closedAfter⟩

/-- The actual right fold derives every head mask and retains its full same-return receipt. -/
theorem fold (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap depth value)
    (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) values) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
  have retained := fold_support formulas solver inventory depth reads coherent active ready admitted available closed
    physicalStored covered valid native merged bounded supported
  have domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values :=
    fun _ _ path _ => SourceCurrentConstrainedCapForestSupport.closed_domains values before.native.machine.heap
      ready.semantic available closed (path.map Int.ofNat)
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
    ready admitted available domains physicalStored covered valid
  exact ⟨next, receipt, retained⟩

/-- The complete actual pass retains all initial masks and caps after literal empty propagation. -/
theorem pass (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap depth value)
    (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) values) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
  cases reads with
  | done lower =>
      obtain ⟨_next, _receipt, nativeAfter, mergeAfter, related, _caps, closedAfter⟩ :=
        fold formulas solver inventory depth lower coherent active ready admitted available closed
          physicalStored covered valid native merged bounded supported
      have propagated := SourceCurrentConstrainedCapForestSupport.trans related
        (SourceCurrentConstrainedCapForestSupport.propagate Plain _)
      have domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values :=
        fun _ _ path _ => SourceCurrentConstrainedCapForestSupport.closed_domains values before.native.machine.heap
          ready.semantic available closed (path.map Int.ofNat)
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory (.done lower)
        coherent active ready admitted available domains physicalStored covered valid
      exact ⟨next, receipt, nativeAfter, mergeAfter, propagated,
        SourceCurrentConstrainedCapMaskCharacterization.children_cap propagated bounded,
        SourceCurrentConstrainedCapForestSupport.closed_transport (SourceCurrentClassFoldDomains.propagate_transport _) closedAfter⟩

end MicroCFTA.SourceCurrentConstrainedCapRichClassPassSupport
