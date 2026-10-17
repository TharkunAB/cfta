import MicroCFTA.SourceCurrentConstrainedCapRichRequiredCompletion
import MicroCFTA.SourceCurrentConstrainedCapForestSupport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RichRequiredCompletionKernels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (advanceHeap)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored

/-- Two arbitrary Required prefixes construct their own returns from the first entry facts. -/
theorem serial [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) {width : Nat}
    (firstPaths secondPaths : List (List Int)) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (memos : Memos)
    (ready : Ready before) (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (native : NativeStored annotation before) (merged : MergeStored annotation memo)
    (bounded : ∀ value ∈ values, Cap annotation depth value)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ middle firstHeap firstMemos results heap final,
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel firstPaths values before.native.machine.heap)
        middle firstHeap ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads firstPaths values middle before.native.machine.heap firstHeap memos firstMemos ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel secondPaths middle firstHeap)
        results heap ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads secondPaths middle results firstHeap heap firstMemos final ∧
      Ready (advanceHeap (advanceHeap before firstHeap) heap) ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advanceHeap (advanceHeap before firstHeap) heap)) ∧
      NativeStored annotation (advanceHeap (advanceHeap before firstHeap) heap) ∧ MergeStored annotation memo ∧
      Language.All₂ (Preserves annotation) values results ∧
      (∀ value ∈ results, Cap annotation depth value) ∧
      (∀ path, ForestSupported annotation path values → ForestSupported annotation path results) ∧
      results.length = values.length ∧ ClosedValues results ∧ EndpointMemoGateTrace.Valid heap final := by
  obtain ⟨middle, firstHeap, firstMemos, firstStable, firstReads, firstValid, _firstUnfolding, _firstQuery,
      firstReady, firstEffects, firstNative, firstMerge, firstRelation, firstCaps, firstMasks,
      _firstOriginals, firstAvailable, firstClosed, firstLength⟩ :=
    SourceCurrentConstrainedCapRichRequiredCompletion.complete annotation depth firstPaths values before memo memos
      ready available closed native merged bounded valid
  obtain ⟨results, heap, final, secondStable, secondReads, secondValid, _secondUnfolding, _secondQuery,
      secondReady, secondEffects, secondNative, secondMerge, secondRelation, secondCaps, secondMasks,
      _secondOriginals, _secondAvailable, secondClosed, secondLength⟩ :=
    SourceCurrentConstrainedCapRichRequiredCompletion.complete annotation depth secondPaths middle
      (advanceHeap before firstHeap) memo firstMemos firstReady firstAvailable firstClosed firstNative firstMerge firstCaps firstValid
  exact ⟨middle, firstHeap, firstMemos, results, heap, final, firstStable, firstReads, secondStable, secondReads,
    secondReady, firstEffects.trans secondEffects, secondNative, secondMerge,
    SourceCurrentConstrainedCapForestSupport.trans firstRelation secondRelation, secondCaps,
    (fun path supported => secondMasks path (firstMasks path supported)), secondLength.trans firstLength, secondClosed, secondValid⟩

end MicroCFTA.RichRequiredCompletionKernels

#print axioms MicroCFTA.RichRequiredCompletionKernels.serial
#check @MicroCFTA.RichRequiredCompletionKernels.serial
