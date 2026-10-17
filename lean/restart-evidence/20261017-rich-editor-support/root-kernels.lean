import MicroCFTA.SourceCurrentConstrainedCapRichClassPassSupport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RichClassCapKernels
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Pass PassReads Receipt)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Initial finite cap and class lengths derive every mask for the same actual mixed-cap pass. -/
theorem long_paths
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (depth : Nat)
    {records values results} {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : SourceCurrentHereditaryNativeUniversalStore.Stored Plain before)
    (merged : SourceCurrentHereditaryMerge.Stored Plain memo)
    (bounded : ∀ value ∈ values, SourceCurrentConstrainedCap.Cap Plain depth value)
    (lengths : ∀ record ∈ records, ∀ path ∈ record.paths, depth + 1 ≤ path.length) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final ∧
      SourceCurrentHereditaryNativeUniversalStore.Stored Plain after ∧ SourceCurrentHereditaryMerge.Stored Plain saved ∧
      All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, SourceCurrentConstrainedCap.Cap Plain depth value) ∧ ClosedValues results := by
  have masks : ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceCurrentConstrainedCapPaths.ForestSupported Plain (path.map Int.ofNat) values := by
    intro record member path present
    have long := lengths record member path present
    cases path with
    | nil => simp only [List.length_nil] at long; omega
    | cons index path =>
        apply SourceCurrentConstrainedCapPaths.forest_of_cap Plain depth values bounded (index : Int) (path.map Int.ofNat)
        simp only [List.length_cons] at long
        simp only [List.length_map]
        omega
  exact SourceCurrentConstrainedCapRichClassPassSupport.pass formulas solver inventory depth reads coherent active
    ready admitted available closed physicalStored covered valid native merged bounded masks

end MicroCFTA.RichClassCapKernels

#print axioms MicroCFTA.RichClassCapKernels.long_paths
#check @MicroCFTA.RichClassCapKernels.long_paths
