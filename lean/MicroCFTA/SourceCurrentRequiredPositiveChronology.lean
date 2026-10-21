import MicroCFTA.SourceCurrentClassPositiveChronology
import MicroCFTA.SourceCurrentConjunctionRequiredClassPass
import MicroCFTA.SourceCurrentRequiredRawCorridor
import MicroCFTA.SourceCurrentRequiredForestPositive
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentNativePositiveSupportAdvance
import MicroCFTA.SourceCurrentRequiredPublicationHistory

/-!
# Actual Required entry for positive class chronology

The same Required return supplies the prepared masks, stores, and causal
history. The completed pass returns a positive occurrence in that capture.
The original Required call retains its forest slot and natural path.
-/
namespace MicroCFTA.SourceCurrentRequiredPositiveChronology
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassPass (Pass PassReads Receipt)
open SourceEqualityProjectionGraph (select)
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support

/-- Actual Required and completed class reads retain positive ancestry to the original forest. -/
theorem pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {width : Nat} {selected : EqualityNormalize.Constraints}
    {originalValues preparedValues results : List Node} {scan prepared after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected
      originalValues preparedValues scan prepared)
    (semantic : SemanticReady scan.native.machine.heap)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal scan.native.machine.heap)
    (costs : CostHeap scan.native.machine.heap) (available : Values scan.native.machine.heap originalValues)
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace source reaches
      originalValues paths scan.native.machine.heap false scan.native.machine.heap)
    (current : Current scan) (supported : NativeSupport scan.native.machine.heap scan.native)
    (causal : History empty scan.native.machine.heap) (records : List SourceEqualityClassOrder.Record)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    {memo saved : Memo} {memos final : Memos}
    {actual : Pass records preparedValues prepared memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (physical : PhysicalStored scan.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid prepared.native.machine.heap memos)
    (merged : MergeStored memo) (positiveMemo : MergeSupport memo) :
    ∃ next, Receipt formulas solver next records preparedValues prepared memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path : List Int, RawCorridor path original → RawCorridor path result) preparedValues results ∧
      NativeSupport after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      ∀ outputIndex result, results[outputIndex]? = some result → ∀ residual, PositiveAt result residual →
        ∃ inputIndex originalPath original, originalValues[inputIndex]? = some original ∧ PositiveAt original originalPath ∧
          Rel selected (outputIndex::residual) (inputIndex::originalPath) := by
  obtain ⟨fuel,readFuel,enough⟩ := required.stable
  have actualRequired := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originalValues scan.native.machine.heap preparedValues prepared.native.machine.heap).mpr
      ⟨fuel,readFuel,actualRequired⟩
  have preparedFacts : Guards prepared.native.machine.heap ∧
      Nonempty (History scan.native.machine.heap prepared.native.machine.heap) := by
    cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
    | node entries =>
      simp only [compiled] at graph
      exact ⟨SourceCurrentRequiredGuard.children Plain graph semantic costs available current.1.guards,
        SourceCurrentRequiredPublicationHistory.children graph semantic costs available⟩
  have preparedCurrent := SourceCurrentConstrainedCapCurrentNative.advance Plain scan prepared current
    required.ready.good required.ready.semantic.ready.semantic preparedFacts.1 required.extension required.nodes required.edges
  have preparedSupport := SourceCurrentNativePositiveSupportAdvance.advance scan prepared current supported
    required.ready.good required.extension required.nodes required.edges
  obtain ⟨interval⟩ := preparedFacts.2
  have preparedHistory : History empty prepared.native.machine.heap := .trans causal interval
  have retained := SourceCurrentRequiredRawCorridor.required actualRequired semantic normal costs available current.1.guards primary
  have masks : ∀ record ∈ records, ∀ index path, index::path ∈ record.paths → ∀ value,
      select preparedValues (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value := by
    intro record member index path included value found
    have chosen : record.paths ∈ selected := selectedEq ▸ List.mem_map.mpr ⟨record,member,rfl⟩
    have natural : preparedValues[index]? = some value := by
      simpa only [select,Int.ofNat_eq_natCast,ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
    obtain ⟨_original,_found,_origin,safe⟩ := retained record.paths chosen index path included value natural
    exact safe
  obtain ⟨next,receipt,currentAfter,mergedAfter,corridors,supportedAfter,causalAfter,positiveAfter,back⟩ :=
    SourceCurrentClassPositiveChronology.pass formulas solver inventory reads coherent active required.ready required.admitted required.resident
      (SourceCurrentConjunctionRequiredClassPass.selected_domains required records selectedEq)
      (physical.grows required.effects.keeps) covered valid preparedCurrent merged masks preparedSupport preparedHistory positiveMemo
  refine ⟨next,receipt,currentAfter,mergedAfter,corridors,supportedAfter,causalAfter,positiveAfter,?_⟩
  intro outputIndex result found residual positive
  obtain ⟨inputIndex,originalPath,preparedValue,preparedFound,preparedPositive,related⟩ := back outputIndex result found residual positive
  obtain ⟨original,originalFound,originalPositive⟩ := SourceCurrentRequiredForestPositive.requireAll actualRequired
    semantic normal costs available current.1.guards primary preparedFound preparedPositive
  exact ⟨inputIndex,originalPath,original,originalFound,originalPositive,by simpa only [selectedEq] using related⟩

end MicroCFTA.SourceCurrentRequiredPositiveChronology
