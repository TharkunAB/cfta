import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourcePruningEnumerationNativeArityPrimitives
import MicroCFTA.SourcePruningEnumerationNativeRequestArity

/-!
# Physical traces for every actual finite native outcome

The physical plan supplies each reached instruction check.
Yielded observations retain their exact trace and current check.
Terminal observations retain the actual shorter prefix and final step.
Only an optional binder can change the constructor heap on a terminal step.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOutcomeTrace
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual finite physical plan derives every reached prefix and exact terminal instruction. -/
theorem execute_readback (fuel : Nat) (control : Control A) (before : Checked width)
    (plan : InputsThrough fuel control before) :
    match execute fuel control before with
    | .yielded next after => Trace fuel control before next after ∧ Inputs next after
    | .done value after => ∃ used, used < fuel ∧ Trace used control before (.code (.pure value)) after
    | .failed failure after => ∃ used last current,
        used < fuel ∧ Trace used control before last current ∧ Inputs last current ∧
          step last current = .failed failure after
    | .constraintError message after => ∃ used last current,
        used < fuel ∧ Trace used control before last current ∧ Inputs last current ∧
          step last current = .constraintError message after
    | .blocked reason next after => ∃ used last current,
        used < fuel ∧ Trace used control before last current ∧ Inputs last current ∧
          step last current = .blocked reason next after := by
  induction fuel generalizing control before with
  | zero => exact ⟨.refl _ _, plan⟩
  | succ fuel ih =>
      have current : Inputs control before := plan.1
      cases one : step control before with
      | yielded next middle =>
          have nextPlan : InputsThrough fuel next middle := by
            simpa only [InputsThrough, one] using plan.2
          have tail := ih next middle nextPlan
          cases result : execute fuel next middle with
          | yielded rest after =>
              simp only [result] at tail
              simp only [execute, one, result]
              exact ⟨.cons control before next middle rest after fuel current one tail.1, tail.2⟩
          | done value after =>
              simp only [result] at tail
              simp only [execute, one, result]
              obtain ⟨used, bounded, traced⟩ := tail
              exact ⟨used + 1, by omega,
                .cons control before next middle (.code (.pure value)) after used current one traced⟩
          | failed failure after =>
              simp only [result] at tail
              simp only [execute, one, result]
              obtain ⟨used, last, reached, bounded, traced, inputs, terminal⟩ := tail
              exact ⟨used + 1, last, reached, by omega,
                .cons control before next middle last reached used current one traced, inputs, terminal⟩
          | constraintError message after =>
              simp only [result] at tail
              simp only [execute, one, result]
              obtain ⟨used, last, reached, bounded, traced, inputs, terminal⟩ := tail
              exact ⟨used + 1, last, reached, by omega,
                .cons control before next middle last reached used current one traced, inputs, terminal⟩
          | blocked reason rest after =>
              simp only [result] at tail
              simp only [execute, one, result]
              obtain ⟨used, last, reached, bounded, traced, inputs, terminal⟩ := tail
              exact ⟨used + 1, last, reached, by omega,
                .cons control before next middle last reached used current one traced, inputs, terminal⟩
      | done value after =>
          simp only [execute, one]
          refine ⟨0, by omega, ?_⟩
          obtain ⟨rfl, rfl⟩ := (step_done_iff control before after value).mp one
          exact .refl _ _
      | failed failure after =>
          simp only [execute, one]
          exact ⟨0, control, before, by omega, .refl _ _, current, one⟩
      | constraintError message after =>
          simp only [execute, one]
          exact ⟨0, control, before, by omega, .refl _ _, current, one⟩
      | blocked reason next after =>
          simp only [execute, one]
          exact ⟨0, control, before, by omega, .refl _ _, current, one⟩

/-- A terminal native step retains arity without a condition on arbitrary work continuations. -/
theorem terminal_step_heap (control : Control A) (before : Checked width)
    (valid : Good before) (heap : Heap before.native.machine.heap)
    (inputs : Inputs control before)
    (terminal : match step control before with | .yielded _ _ => False | _ => True) :
    Heap (step control before).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      change Heap (body request next before).state.native.machine.heap
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact heap
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact heap
      | work job next =>
          change False at terminal
          exact terminal.elim
      | optionalBinder key body next =>
          exact SourcePruningEnumerationNativeArityPrimitives.step_optionalBinder_heap key body next before
            valid.heap.semantic.1.normal.facts heap inputs
      | node request next =>
          rw [SourcePruningEnumerationNativeRequestArity.node_step_heap]
          exact heap
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact heap

end MicroCFTA.SourcePruningEnumerationNativeOutcomeTrace
