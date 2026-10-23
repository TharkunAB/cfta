import MicroCFTA.SourceRecursiveIntersectionNativeNodeCounterGrowth
import MicroCFTA.SourceEqualityNativeDemandHeap

namespace MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat} {Output : Type}

/-- Lifting an actual native outcome retains its complete native state. -/
private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (SourceEqualityNativeDemand.lift operations outcome).state.native = outcome.state := by
  cases outcome <;> rfl

/-- One checked-demand step retains or increases its actual constructor node counter. -/
theorem step_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : SourceEqualityNativeDemand.Control Output)
    (state : SourceEqualityNativeDemand.State width) :
    state.native.machine.heap.nodes.next ≤
      (SourceEqualityNativeDemand.step control state).state.native.machine.heap.nodes.next := by
  cases control with
  | code code =>
      have nativeGrowth : state.native.machine.heap.nodes.next ≤
          (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
            SourceEqualityPCSNativeEdge.conjoin code state.native).state.machine.heap.nodes.next := by
        exact SourceRecursiveIntersectionNativeNodeCounterGrowth.step_mono
          SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin code state.native
      cases code with
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          simpa only [SourceRecursiveIntersectionNative.edge_step_machine] using nativeGrowth
      | pure | fail | work | enter | read | optionalBinder | node | finishNode | finishEdge =>
          simpa only [SourceEqualityNativeDemand.step, lift_native] using nativeGrowth
  | edgeBody request next =>
      change state.native.machine.heap.nodes.next ≤
        (SourceEqualityNativeDemand.body request next state).state.native.machine.heap.nodes.next
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact Nat.le_refl _

/-- Every finite checked-demand outcome retains or increases its input node counter. -/
theorem execute_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : SourceEqualityNativeDemand.Control Output)
    (state : SourceEqualityNativeDemand.State width) :
    state.native.machine.heap.nodes.next ≤
      (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap.nodes.next := by
  induction fuel generalizing control state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      have first : state.native.machine.heap.nodes.next ≤
          (SourceEqualityNativeDemand.step control state).state.native.machine.heap.nodes.next := by
        exact step_mono control state
      cases observed : SourceEqualityNativeDemand.step control state with
      | yielded next after =>
          simp only [observed, SourceEqualityNativeDemand.Outcome.state] at first
          simpa only [SourceEqualityNativeDemand.execute, observed] using
            Nat.le_trans first (ih next after)
      | done value after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | failed failure after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | constraintError message after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first
      | blocked reason next after =>
          simpa only [SourceEqualityNativeDemand.execute, observed,
            SourceEqualityNativeDemand.Outcome.state] using first

/-- Resumption retains or increases the node counter in its supplied outcome state. -/
theorem resume_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (outcome : SourceEqualityNativeDemand.Outcome width Output) :
    outcome.state.native.machine.heap.nodes.next ≤
      (SourceEqualityNativeDemand.resume fuel outcome).state.native.machine.heap.nodes.next := by
  cases outcome with
  | yielded next after => exact execute_mono fuel next after
  | done | failed | constraintError | blocked => exact Nat.le_refl _

end MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.step_mono
#print MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.step_mono
#print axioms MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.step_mono
#check @MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.execute_mono
#print MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.execute_mono
#print axioms MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.execute_mono
#check @MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.resume_mono
#print MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.resume_mono
#print axioms MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth.resume_mono
