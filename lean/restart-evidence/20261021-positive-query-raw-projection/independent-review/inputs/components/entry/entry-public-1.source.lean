import MicroCFTA.SourceCurrentClassCorridorChronology
import MicroCFTA.SourceCurrentConjunctionRequiredClassPass

/-!
# Actual Required entry for chronological class corridors

The Required receipt supplies the literal prepared return and every path
domain. Original false gates supply raw masks at that same return. The
actual class pass retains those corridors through its literal tail states.
-/
namespace MicroCFTA.SourceCurrentRequiredCorridorChronology
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassPass (Pass PassReads Receipt)
open SourceEqualityProjectionGraph (select)
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => State Symbol Guard
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
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap

/-- Original Required gates derive the masks and domains for the same actual class pass. -/
theorem pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {width : Nat} {selected : EqualityNormalize.Constraints}
    {originalValues preparedValues results : List Node}
    {scan : Checked width} {preparedHeap : Heap}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected
      originalValues preparedValues scan (advanceHeap scan preparedHeap))
    (semantic : SemanticReady scan.native.machine.heap)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal scan.native.machine.heap)
    (costs : CostHeap scan.native.machine.heap)
    (available : Values scan.native.machine.heap originalValues)
    (guards : Guards scan.native.machine.heap)
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace source reaches
      originalValues paths scan.native.machine.heap false scan.native.machine.heap)
    (records : List SourceEqualityClassOrder.Record)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    {memo saved : Memo} {after : Checked width} {memos final : Memos}
    {actual : Pass records preparedValues (advanceHeap scan preparedHeap) memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (physical : PhysicalStored scan.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid preparedHeap memos)
    (current : Current (advanceHeap scan preparedHeap))
    (merged : MergeStored memo) :
    ∃ next, Receipt formulas solver next records preparedValues
      (advanceHeap scan preparedHeap) memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧
      All₂ (fun original result => ∀ path : List Int,
        RawCorridor path original → RawCorridor path result) preparedValues results := by
  obtain ⟨fuel, readFuel, enough⟩ := required.stable
  have actualRequired := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have retained := SourceCurrentRequiredRawCorridor.required actualRequired
    semantic normal costs available guards primary
  have masks : ∀ record ∈ records, ∀ index path, index :: path ∈ record.paths → ∀ value,
      select preparedValues (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value := by
    intro record member index path included value found
    have chosen : record.paths ∈ selected :=
      selectedEq ▸ List.mem_map.mpr ⟨record, member, rfl⟩
    have natural : preparedValues[index]? = some value := by
      simpa only [select, Int.ofNat_eq_natCast,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)), Int.toNat_natCast] using found
    obtain ⟨_original, _found, _origin, safe⟩ := retained record.paths chosen index path included value natural
    exact safe
  exact SourceCurrentClassCorridorChronology.pass formulas solver inventory reads coherent active
    required.ready required.admitted required.resident
    (SourceCurrentConjunctionRequiredClassPass.selected_domains required records selectedEq)
    (physical.grows required.effects.keeps) covered valid current merged masks

end MicroCFTA.SourceCurrentRequiredCorridorChronology

set_option linter.all true
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentRequiredCorridorChronology.pass
#print MicroCFTA.SourceCurrentRequiredCorridorChronology.pass
#print axioms MicroCFTA.SourceCurrentRequiredCorridorChronology.pass
