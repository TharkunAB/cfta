import MicroCFTA.SourceCurrentConstrainedCapRichRequiredCompletion
import MicroCFTA.SourceCurrentConstrainedCapRichRequiredClassPass

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.IndependentFinalRichKernels
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentConjunctionClassScan (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained

/-- Initial selected facts construct the Required prefix and its exact class-pass entry laws. -/
theorem required_then_pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (depth : Nat) (records : List SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap originals) (closed : ClosedValues originals)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (proper : ∀ path ∈ (records.map SourceEqualityClassOrder.Record.paths).flatten, path ≠ [])
    (primary : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches originals paths before.native.machine.heap false before.native.machine.heap)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ originals, Cap depth value)
    (supported : ∀ record ∈ records, ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) :
    ∃ values heap current,
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) originals before.native.machine.heap)
        values heap ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths))
        originals values before.native.machine.heap heap memos current ∧
      EndpointMemoGateTrace.Valid heap current ∧
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory (records.map SourceEqualityClassOrder.Record.paths)
        originals values before (advanceHeap before heap) ∧
      ∀ results after saved final (actual : SourceCurrentAllocatedClassPass.Pass records values (advanceHeap before heap) memo results after saved),
        SourceCurrentAllocatedClassPass.PassReads formulas solver actual current final →
        ∃ next, SourceCurrentConjunctionRequiredClassPass.Receipt formulas solver next records
            (records.map SourceEqualityClassOrder.Record.paths) originals values before (advanceHeap before heap) memo results after saved current final ∧
          NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) originals results ∧
          (∀ value ∈ results, Cap depth value) ∧ ClosedValues results ∧
          ∀ path, ForestSupported Plain path originals → ForestSupported Plain path results := by
  obtain ⟨requiredValues, requiredHeap, required⟩ :=
    SourceCurrentConjunctionRequired.required_complete formulas solver inventory unconstrained reaches
      (records.map SourceEqualityClassOrder.Record.paths) originals before ready admitted available proper primary
  obtain ⟨values, heap, current, stable, reads, currentValid, _unfolding, _query,
      _preparedReady, _effects, _preparedNative, _preparedMerge, _relation, _caps, _masks,
      _originalsAvailable, _valuesAvailable, _valuesClosed, _length⟩ :=
    SourceCurrentConstrainedCapRichRequiredCompletion.complete Plain depth
      (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths))
      originals before memo memos ready available closed native merged bounded valid
  have same := SourceEqualityRequiredExecution.stable_unique stable required.stable
  have ownRequired : SourceCurrentConjunctionRequired.Receipt formulas solver inventory
      (records.map SourceEqualityClassOrder.Record.paths) originals values before (advanceHeap before heap) := by
    rw [same.1, same.2]
    exact required
  refine ⟨values, heap, current, stable, reads, currentValid, ownRequired, ?_⟩
  intro results after saved final actual passReads
  obtain ⟨next, receipt, nativeAfter, mergeAfter, relation, caps, resultClosed⟩ :=
    SourceCurrentConstrainedCapRichRequiredClassPass.verified formulas solver inventory depth records
      ownRequired reads rfl coherent active passReads ready available closed physicalStored covered currentValid native merged bounded supported
  exact ⟨next, receipt, nativeAfter, mergeAfter, relation, caps, resultClosed,
    SourceCurrentConstrainedCapRequiredSupport.forest_supported Plain relation⟩

end MicroCFTA.IndependentFinalRichKernels

#print axioms MicroCFTA.IndependentFinalRichKernels.required_then_pass
#check @MicroCFTA.IndependentFinalRichKernels.required_then_pass
