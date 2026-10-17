import MicroCFTA.SourceCurrentConstrainedCapRichEditSupport
import MicroCFTA.SourceCurrentConstrainedCapForestSupport
import MicroCFTA.SourceCurrentAllocatedClassEdits

/-!
# Actual compiled classes retain rich stores and all original masks

Each class clears only its local slots. The literal compiled edit reads
derive all leaf laws from the captured original masks and causal tables.
The result retains the full physical and language receipt at the same return.
This verifies supplied class reads. It does not assert finite completion.
The hereditary leaf family is smaller than the complete source gate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichClassSupport
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
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

/-- Initial class masks derive the actual compiled leaves and all same-return causal laws. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (depth : Nat)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap depth value)
    (supported : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) values) :
    ∃ next, Receipt formulas solver next record values before memo results after saved memos final ∧
      NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results := by
  cases reads with
  | edit lower =>
      have domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values :=
        fun path _ => SourceCurrentConstrainedCapForestSupport.closed_domains values before.native.machine.heap
          ready.semantic available closed (path.map Int.ofNat)
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
        formulas solver inventory record values before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physicalStored covered
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      have placed : SourceCurrentConstrainedCapEditSupport.ListAtLeaves Plain (compiled record) values :=
        SourceCurrentConstrainedCapEditSupport.class_placement Plain record coherent active id values supported
      have initialStored := SourceCurrentConstrainedCapSharedSupport.initial_stored record values before memo native merged
      have produced := SourceCurrentConstrainedCapRichEditSupport.list lower inventory depth
        (compiled_populated record) (compiled_allowed record) initialReady available safe valid
        available closed supported initialStored bounded placed
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record
        coherent active (.edit lower) ready admitted available domains physicalStored covered valid
      exact ⟨next, receipt, produced.1.native, produced.1.merge, produced.2.1, produced.2.2,
        SourceCurrentConstrainedCapForestSupport.closed_transport receipt.transport closed⟩

end MicroCFTA.SourceCurrentConstrainedCapRichClassSupport
