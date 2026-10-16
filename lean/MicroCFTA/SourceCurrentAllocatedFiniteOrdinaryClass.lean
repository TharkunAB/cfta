import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
import MicroCFTA.SourceCurrentAllocatedClassEdits

/-!
# Finite ordinary structure through one actual class

The class captures its actual entry forest. Initialization clears only
its local target slots. The native and merge tables retain their existing
structural certificates. The literal compiler and actual edit reads derive
all intermediate domains and positional height bounds.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads ClassRanges Receipt)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
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

/-- Supplied actual class reads retain structural tables and every original forest position. -/
theorem verified (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next record values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record coherent active reads
    ready admitted available domains physical covered valid
  have structural : NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
    cases reads with
    | edit lower =>
        have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
          before.native.machine.heap before memo ready admitted
          (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
        have initialStored := SourceCurrentAllocatedFiniteOrdinaryShared.initial_stored before memo native merged
        have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
          obtain ⟨entries, built⟩ := compiled_children record coherent active
          rw [built]
          exact compiled_safe record coherent values domains entries built
        obtain ⟨returned, related⟩ := SourceCurrentAllocatedFiniteOrdinaryEdits.list lower
          (compiled_populated record) (compiled_allowed record) initialReady available safe valid
          available domain initialStored domain
        exact ⟨returned.native, returned.merge, related⟩
  exact ⟨next, receipt, structural⟩

/-- Initial forest and table facts construct the compiled class with derived positional bounds. -/
theorem finite (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (ranges : ClassRanges record values before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  obtain ⟨results, after, saved, _, final, actual, reads, _⟩ := SourceCurrentAllocatedClassEdits.finite
    formulas solver inventory record coherent active values before memo ready admitted available domains physical covered ranges memos valid
  obtain ⟨next, receipt, nativeAfter, mergeAfter, related⟩ := verified formulas solver inventory record coherent active reads
    ready admitted available domain physical covered native merged valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt, nativeAfter, mergeAfter, related⟩
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass
