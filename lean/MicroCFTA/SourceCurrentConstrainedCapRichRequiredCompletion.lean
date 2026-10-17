import MicroCFTA.SourceCurrentConstrainedCapRichRequiredSupport

/-!
# Initial facts construct the rich Required prefix

The literal worker accepts arbitrary signed paths and closed forests.
Its own returned execution supplies the actual read receipts.
The same constructor effects derive checked readiness at the class entry.
No completed graph or future class result is an input.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichRequiredCompletion
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
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored

/-- Initial closed local facts construct the exact Required return and every rich class-entry law. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) {width : Nat}
    (paths : List (List Int)) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (memos : Memos)
    (ready : Ready before) (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (native : NativeStored annotation before) (merged : MergeStored annotation memo)
    (bounded : ∀ value ∈ values, Cap annotation depth value)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ results heap final,
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before.native.machine.heap)
        results heap ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before.native.machine.heap heap memos final ∧
      EndpointMemoGateTrace.Valid heap final ∧
      Cache.Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Ready (advanceHeap before heap) ∧ Effects (physical before) (physical (advanceHeap before heap)) ∧
      NativeStored annotation (advanceHeap before heap) ∧ MergeStored annotation memo ∧
      Language.All₂ (Preserves annotation) values results ∧
      (∀ value ∈ results, Cap annotation depth value) ∧
      (∀ path, ForestSupported annotation path values → ForestSupported annotation path results) ∧
      Values heap values ∧ Values heap results ∧ ClosedValues results ∧ results.length = values.length := by
  obtain ⟨results, heap, kept, resident, outputClosed, stable⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete paths values before.native.machine.heap ready.semantic.ready available closed
  have stableRun := stable
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨final, reads, finalValid, unfolding, querySame⟩ :=
    SourceCurrentRequiredQueryMemos.requireAll_memos fuel readFuel paths values results before.native.machine.heap heap
      done ready.semantic ready.costs available memos valid
  have fields := SourceCurrentRequiredHeapEffects.requireAll
    (SourceCurrentConjunctionEquality.FieldAvailable before.operations)
    fuel readFuel paths values results before.native.machine.heap heap done
    ready.semantic ready.costs ready.good.fields available
  have effects : Effects (physical before) ⟨heap, before.operations⟩ :=
    ⟨fields.1, ⟨fields.2.1, fields.2.2.1, ready.good.operations, fields.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl before.operations⟩
  have returned := SourceCurrentConstrainedCapRichRequiredSupport.requireAll annotation depth reads
    ready available closed native merged bounded
  exact ⟨results, heap, final, stableRun, reads, finalValid, unfolding, querySame,
    SourceCurrentConjunctionClassScan.advance_ready before ⟨heap, before.operations⟩ ready effects, effects,
    returned.1, returned.2.1, returned.2.2.1, returned.2.2.2.1, returned.2.2.2.2,
    (fun value member => kept.available value (available value member)), resident, outputClosed,
    returned.2.2.1.length_eq.symm⟩

end MicroCFTA.SourceCurrentConstrainedCapRichRequiredCompletion
