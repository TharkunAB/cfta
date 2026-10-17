import MicroCFTA.SourceCurrentConstrainedCapRichRequiredSupport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RichRequiredKernels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored
local notation "ForestSupported" => SourceCurrentConstrainedCapPaths.ForestSupported

/-- Initial facts construct signed Required calls on repeated positions and retain their exact rich return. -/
theorem constructed_signed_repeated_prefix [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) {width : Nat}
    (left right : Value Symbol Guard) (before : Checked width) (memo : Memo) (memos : Memos)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (available : Values before.native.machine.heap [left, right, left])
    (closed : ClosedValues [left, right, left])
    (native : NativeStored annotation before) (merged : MergeStored annotation memo)
    (bounded : ∀ value ∈ [left, right, left], Cap annotation depth value)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ results heap final,
      SourceCurrentRequiredQueryMemos.RequireAllReads [[-1, 0], [0, 1]] [left, right, left] results
        before.native.machine.heap heap memos final ∧
      EndpointMemoGateTrace.Valid heap final ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel headFuel => SourceEqualityRequiredExecution.requireAll fuel headFuel [[-1, 0], [0, 1]]
          [left, right, left] before.native.machine.heap) results heap ∧
      NativeStored annotation (SourceCurrentConjunctionClassScan.advanceHeap before heap) ∧
      MergeStored annotation memo ∧ Language.All₂ (Preserves annotation) [left, right, left] results ∧
      (∀ value ∈ results, Cap annotation depth value) ∧
      (∀ path, ForestSupported annotation path [left, right, left] → ForestSupported annotation path results) ∧
      results.length = 3 ∧ ClosedValues results := by
  obtain ⟨results, heap, _keeps, _resident, outputClosed, stable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete [[-1, 0], [0, 1]] [left, right, left]
      before.native.machine.heap ready.semantic.ready available closed
  obtain ⟨fuel, headFuel, enough⟩ := stable
  have done := enough fuel headFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨final, reads, finalValid, _unfolding, _queries⟩ :=
    SourceCurrentRequiredQueryMemos.requireAll_memos fuel headFuel [[-1, 0], [0, 1]] [left, right, left]
      results before.native.machine.heap heap done ready.semantic ready.costs available memos valid
  have returned := SourceCurrentConstrainedCapRichRequiredSupport.requireAll annotation depth reads
    ready available closed native merged bounded
  exact ⟨results, heap, final, reads, finalValid, fuel, headFuel, enough,
    returned.1, returned.2.1, returned.2.2.1, returned.2.2.2.1, returned.2.2.2.2,
    returned.2.2.1.length_eq.symm, outputClosed⟩

end MicroCFTA.RichRequiredKernels

#print axioms MicroCFTA.RichRequiredKernels.constructed_signed_repeated_prefix
#check @MicroCFTA.RichRequiredKernels.constructed_signed_repeated_prefix
