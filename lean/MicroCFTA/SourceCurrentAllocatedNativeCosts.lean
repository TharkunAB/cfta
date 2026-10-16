import MicroCFTA.SourceRecursiveIntersectionCostEffects
import MicroCFTA.SourceEqualityNativeDemandFieldExecution

/-!
# Stored cost heaps through checked native demand

Ordinary constructor jobs retain every stored Mu cost observation. Optional
binders use the actual fresh constructor cost proof. Checked edge bodies
change equality operations and leave the constructor heap unchanged.

The induction follows the actual checked step and every finite outcome.
Its input checks concern current physical constructor operands. It needs
no closed input, final cost heap, completed callback, or old native replay.
CostHeap records stored unfolding observations. It is not a runtime bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCosts
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Actual primitive work retains stored costs from its current constructor classification. -/
theorem work_costs {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard Output) (heap : State Symbol Guard)
    (costs : CostHeap heap) (inputs : WorkInputs heap job) : CostHeap (run job heap).2 := by
  cases inputs with
  | pure => exact costs
  | edge => exact costs
  | node edges resident =>
      exact InternedFreshOrdinaryCostHeap.preserve heap _ costs (InternedShallowHeap.makeNode_noNewMu edges heap)
  | union values available =>
      exact InternedFreshOrdinaryCostHeap.preserve heap _ costs (InternedShallowHeap.makeUnion_noNewMu values heap)

open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityRequiredCache (Ready Keeps)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceEqualityNativeDemandHeap.Inputs
local notation "InputsThrough" => SourceEqualityNativeDemandHeap.InputsThrough

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- Every checked step retains stored costs from initial heap readiness and current physical checks. -/
theorem step_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width) (ready : Ready state.native.machine.heap)
    (costs : CostHeap state.native.machine.heap) (inputs : Inputs control state) :
    CostHeap (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact costs
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact costs
      | work job next =>
          change CostHeap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact work_costs job state.native.machine.heap costs inputs
      | optionalBinder pair body next =>
          have retained := SourceRecursiveIntersectionCostEffects.optionalBinder pair body state.native.machine.heap
            ready.semantic costs inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [actual, InternedNestedConstruction.Outcome.state, step,
                SourceRecursiveIntersectionNative.step, lift, Outcome.state, advance] using retained
      | node request next =>
          change CostHeap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact costs
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact costs

/-- Initial stored costs survive every finite checked execution under its actual reached physical checks. -/
theorem execute_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width) (ready : Ready state.native.machine.heap)
    (costs : CostHeap state.native.machine.heap) (inputs : InputsThrough fuel control state) :
    CostHeap (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact costs
  | succ fuel ih =>
      have one := step_costs control state ready costs inputs.1
      have kept := SourceEqualityNativeDemandHeap.step_keeps control state ready inputs.1
      cases observed : step control state with
      | yielded next after =>
          have nextCosts : CostHeap after.native.machine.heap := by simpa only [observed, Outcome.state] using one
          have nextReady : Ready after.native.machine.heap := by simpa only [observed, Outcome.state] using kept.ready
          have nextInputs : InputsThrough fuel next after := by simpa only [observed] using inputs.2
          simpa only [execute, observed] using ih next after nextReady nextCosts nextInputs
      | done | failed | constraintError | blocked =>
          simpa only [execute, observed, Outcome.state] using one

/-- Existing current-input plans imply the smaller physical plan used by cost preservation. -/
theorem physical_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    InputsThrough fuel control state := by
  induction fuel generalizing control state with
  | zero => exact SourceEqualityNativeDemandValidity.inputs_heap holds control state inputs
  | succ fuel ih =>
      refine ⟨SourceEqualityNativeDemandValidity.inputs_heap holds control state inputs.1, ?_⟩
      cases observed : step control state with
      | yielded next after =>
          exact ih next after (by simpa only [SourceEqualityNativeDemandFieldExecution.InputsThrough, observed] using inputs.2)
      | done | failed | constraintError | blocked => trivial

/-- A valid initial checked state and its reached input plan derive final stored costs on every outcome. -/
theorem execute_costs_of_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (valid : SourceEqualityNativeDemandValidity.StateValid holds state)
    (costs : CostHeap state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    CostHeap (execute fuel control state).state.native.machine.heap :=
  execute_costs fuel control state valid.heap costs (physical_inputs holds fuel control state inputs)

/-- An observed successful checked execution inherits costs from its initial state and actual reached checks. -/
theorem done_costs_of_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output)
    (before after : CheckedState width) (result : Output)
    (valid : SourceEqualityNativeDemandValidity.StateValid holds before)
    (costs : CostHeap before.native.machine.heap)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control before)
    (done : execute fuel control before = .done result after) : CostHeap after.native.machine.heap := by
  simpa only [done, Outcome.state] using execute_costs_of_inputs holds fuel control before valid costs inputs

end MicroCFTA.SourceCurrentAllocatedNativeCosts
