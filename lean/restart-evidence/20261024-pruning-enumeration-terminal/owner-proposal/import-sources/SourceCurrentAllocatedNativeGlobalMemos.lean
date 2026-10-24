import MicroCFTA.SourceNativeGlobalUnfold
import MicroCFTA.SourceQueryUnfoldMemo
import MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Global unfolding receipts through actual checked native traces

Ordinary instructions execute their actual constructor primitives. Checked
edge publication and constraint checks do not change the constructor heap.
The actual checked trace therefore derives an operational constructor trace
with no global unfolding call. Its heap growth retains the same three
global tables. Native request tables and equality operations remain separate.
These results do not describe delayed Haskell operand producers.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeGlobalMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width : Nat} {A : Type}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- Every actual checked instruction derives real primitive execution and absence of global unfolding. -/
theorem step_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state : Checked width) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    ∃ events, SourceGlobalUnfold.Runs ⟨state.native.machine.heap, memo⟩
      ⟨(step control state).state.native.machine.heap, memo⟩ events ∧ SourceGlobalUnfold.NoGlobal events := by
  cases control with
  | edgeBody request next =>
      refine ⟨[], ?_, SourceGlobalUnfold.NoGlobal.nil⟩
      have same := SourceEqualityNativeDemandOperations.body_native request next state
      simpa only [step, same] using (SourceGlobalUnfold.Runs.nil ⟨state.native.machine.heap, memo⟩)
  | code code =>
      have runs := SourceNativeGlobalUnfold.step_runs SourceEqualityConstraintConstructors.top
        SourceEqualityPCSNativeEdge.conjoin code state.native memo
      have silent := SourceNativeGlobalUnfold.step_silent SourceEqualityConstraintConstructors.top
        SourceEqualityPCSNativeEdge.conjoin code state.native
      rw [SourceNativeGlobalUnfold.step_erase] at runs
      cases code with
      | edge request next =>
          refine ⟨[], ?_, SourceGlobalUnfold.NoGlobal.nil⟩
          have empty : SourceGlobalUnfold.Runs ⟨state.native.machine.heap, memo⟩
              ⟨state.native.machine.heap, memo⟩ [] := .nil _
          cases selected : lookupEdge width request state.native with
          | mk handle chosen =>
              have chosenHeap : chosen.machine.heap = state.native.machine.heap := by
                simpa only [selected] using SourceNativeGlobalUnfold.lookupEdge_heap request state.native
              cases demanded : demandEdge handle chosen with
              | mk observation reached =>
                  have reachedHeap : reached.machine.heap = state.native.machine.heap := by
                    simpa only [demanded, chosenHeap] using SourceNativeGlobalUnfold.demandEdge_heap handle chosen
                  cases observation <;> simpa only [step, selected, demanded, Outcome.state, reachedHeap] using empty
      | pure | fail | work | enter | read | optionalBinder | node | finishNode | finishEdge =>
          exact ⟨_, by simpa only [step, lift_heap] using runs, silent⟩

/-- An actual checked trace composes its exact primitive effects without a global unfold call. -/
theorem trace_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control next : Control A} {before after : Checked width}
    (trace : Trace fuel control before next after) (memo : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard) :
    ∃ events, SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memo⟩
      ⟨after.native.machine.heap, memo⟩ events ∧ SourceGlobalUnfold.NoGlobal events := by
  induction trace with
  | refl => exact ⟨[], .nil _, SourceGlobalUnfold.NoGlobal.nil⟩
  | cons control before next middle final after fuel inputs one rest ih =>
      obtain ⟨first, runs, silent⟩ := step_receipt control before memo
      have exactRuns : SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memo⟩
          ⟨middle.native.machine.heap, memo⟩ first := by simpa only [one, Outcome.state] using runs
      obtain ⟨tail, remaining, quiet⟩ := ih
      exact ⟨first ++ tail, exactRuns.append remaining, silent.append quiet⟩

/-- A checked return derives coherence of the same three global tables from initial invariants. -/
theorem trace_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (costs : CostHeap before.native.machine.heap)
    (fields : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ events, SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memos.unfolding⟩
      ⟨after.native.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events ∧
      Valid after.native.machine.heap memos := by
  obtain ⟨events, runs, silent⟩ := trace_receipt trace memos.unfolding
  have effects := SourceCurrentAllocatedNativeTraceEffects.effects trace good semantic costs fields
  exact ⟨events, runs, silent, SourceQueryUnfoldMemo.valid_grows before.native.machine.heap after.native.machine.heap
    semantic effects.2.1.keeps memos valid⟩

end MicroCFTA.SourceCurrentAllocatedNativeGlobalMemos
