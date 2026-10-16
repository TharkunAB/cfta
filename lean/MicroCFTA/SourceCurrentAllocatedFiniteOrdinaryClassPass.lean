import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Positional finite ordinary bounds through the current class pass

Each head class captures the actual tail return. The tail derives that
forest's domain, readiness, and stored native and merge certificates.
Final empty propagation retains positions and cannot increase height.
Supplied read verification needs no range plan. Finite construction uses
only the existing checks at actual reached prefixes.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Ranges Receipt)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_refl forest_trans forest_domain forest_propagate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem fold_structure (inventory : Inventory) {records values results}
    {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Fold records values before memo results after saved} (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos) :
    NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  induction reads generalizing inventory with
  | nil => exact ⟨native, merged, forest_refl domain⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      obtain ⟨firstNative, firstMerge, firstRelation⟩ := ih inventory tailCoherent tailActive
        ready admitted available domain physical covered native merged valid
      obtain ⟨next, firstReceipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first tailCoherent tailActive
        ready admitted available (fun own _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _
          ready.semantic values available domain (path.map Int.ofNat)) physical covered valid
      obtain ⟨_, _, lastNative, lastMerge, lastRelation⟩ := SourceCurrentAllocatedFiniteOrdinaryClass.verified
        formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) last
        firstReceipt.ready firstReceipt.admitted firstReceipt.available (forest_domain firstRelation)
        firstReceipt.stored firstReceipt.covered firstNative firstMerge firstReceipt.globals.valid
      exact ⟨lastNative, lastMerge, forest_trans firstRelation lastRelation⟩

/-- The same actual right fold retains both structural caches and all original positional bounds. -/
theorem fold (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
    ready admitted available (fun own _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _
      ready.semantic values available domain (path.map Int.ofNat)) physical covered valid
  exact ⟨next, receipt, fold_structure formulas solver inventory reads coherent active
    ready admitted available domain physical covered native merged valid⟩

/-- Final propagation retains the same actual pass receipt and its original forest height bounds. -/
theorem pass (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory reads coherent active
    ready admitted available (fun own _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _
      ready.semantic values available domain (path.map Int.ofNat)) physical covered valid
  have structural : NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
    cases reads with
    | done remaining =>
        have checked := fold_structure formulas solver inventory remaining coherent active
          ready admitted available domain physical covered native merged valid
        exact ⟨checked.1, checked.2.1, forest_trans checked.2.2 (forest_propagate (forest_domain checked.2.2))⟩
  exact ⟨next, receipt, structural⟩

/-- Initial domains and actual-tail checks construct a finite right fold with positional bounds. -/
theorem fold_finite (inventory : Inventory) {records values} {before : Checked width} {memo : Memo}
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧ Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨results, after, saved, _, final, actual, reads, _⟩ := SourceCurrentAllocatedClassPass.fold_complete
    formulas solver inventory ranges coherent active ready admitted available
    (fun own _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _)
    physical covered memos valid
  obtain ⟨next, receipt, nativeAfter, mergeAfter, related⟩ := fold formulas solver inventory reads coherent active
    ready admitted available domain physical covered native merged valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt, nativeAfter, mergeAfter, related⟩

/-- Initial structure and reached checks construct the actual full pass with all structural facts derived. -/
theorem finite (inventory : Inventory) {records values} {before : Checked width} {memo : Memo}
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧ Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨results, after, saved, _, final, actual, reads, _⟩ := SourceCurrentAllocatedClassPass.pass_complete
    formulas solver inventory ranges coherent active ready admitted available
    (fun own _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _)
    physical covered memos valid
  obtain ⟨next, receipt, nativeAfter, mergeAfter, related⟩ := pass formulas solver inventory reads coherent active
    ready admitted available domain physical covered native merged valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt, nativeAfter, mergeAfter, related⟩
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
