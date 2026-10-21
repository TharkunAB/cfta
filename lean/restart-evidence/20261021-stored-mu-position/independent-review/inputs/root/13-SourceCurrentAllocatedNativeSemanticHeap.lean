import MicroCFTA.SourceCurrentAllocatedNativeFieldExecution
import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.SourceRecursiveIntersectionGuardedEffects
import MicroCFTA.SourceRecursiveIntersectionBudgetEffects

/-!
# Semantic heaps through actual checked native demand

Current physical work inputs preserve semantic readiness. Optional binders
use the actual guarded and budget heap laws for available open bodies.
The finite proof follows only actual yielded controls. It preserves the
returned heap on errors and blocked outcomes without assuming completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)

/-- Current primitive work inputs retain every component of semantic readiness. -/
theorem work_semantic [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticReady state)
    (inputs : WorkInputs state job) : SemanticReady (run job state).2 := by
  cases inputs with
  | pure => exact semantic
  | edge symbol guard values available =>
      exact SourceEqualityRequiredSemanticCache.edge symbol guard values state semantic available
  | node edges resident =>
      exact ⟨(SourceEqualityNativeDemandHeapPrimitives.node edges state semantic.ready resident).1.ready,
        InternedGuardedProbeHeap.preserve state _ semantic.guarded (InternedShallowHeap.makeNode_noNewMu edges state),
        InternedGuardedBudgetProbeHeap.preserve state _ semantic.budget (InternedShallowHeap.makeNode_noNewMu edges state)⟩
  | union values available =>
      exact ⟨(SourceEqualityNativeDemandHeapPrimitives.union values state semantic.ready available).1.ready,
        InternedGuardedProbeHeap.preserve state _ semantic.guarded (InternedShallowHeap.makeUnion_noNewMu values state),
        InternedGuardedBudgetProbeHeap.preserve state _ semantic.budget (InternedShallowHeap.makeUnion_noNewMu values state)⟩

/-- Actual optional binding retains semantic readiness for every available body. -/
theorem optionalBinder_semantic [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat)
    (body : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticReady state) (available : Available state body) :
    SemanticReady (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state :=
  ⟨(SourceEqualityNativeDemandHeapPrimitives.optionalBinder_keeps pair body state semantic.ready available).ready,
    SourceRecursiveIntersectionGuardedEffects.optionalBinder pair body state semantic.ready.semantic semantic.guarded available,
    SourceRecursiveIntersectionBudgetEffects.optionalBinder pair body state semantic.ready.semantic semantic.budget available⟩

open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- One actual checked instruction retains semantic readiness from its current physical inputs. -/
theorem step_semantic [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : CheckedState width) (semantic : SemanticReady state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.Inputs control state) :
    SemanticReady (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact semantic
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact semantic
      | work job next =>
          change SemanticReady
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact work_semantic job state.native.machine.heap semantic inputs
      | optionalBinder pair body next =>
          have retained := optionalBinder_semantic pair body state.native.machine.heap semantic inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state, advance,
                InternedNestedConstruction.Outcome.state] using retained
      | node request next =>
          change SemanticReady
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact semantic
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact semantic

/-- Every finite actual checked outcome retains semantic readiness without a completion premise. -/
theorem execute_semantic [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (semantic : SemanticReady state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control state) :
    SemanticReady (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact semantic
  | succ fuel ih =>
      have one := step_semantic control state semantic inputs.1
      cases actual : step control state with
      | yielded next after =>
          have current : SemanticReady after.native.machine.heap := by
            simpa only [actual, Outcome.state] using one
          have remaining : SourceEqualityNativeDemandHeap.InputsThrough fuel next after := by
            simpa only [SourceEqualityNativeDemandHeap.InputsThrough, actual] using inputs.2
          simpa only [execute, actual] using ih next after current remaining
      | done | failed | constraintError | blocked =>
          simpa only [execute, actual, Outcome.state] using one

private theorem physical_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    SourceEqualityNativeDemandHeap.InputsThrough fuel control state := by
  induction fuel generalizing control state with
  | zero => exact SourceEqualityNativeDemandValidity.inputs_heap holds control state inputs
  | succ fuel ih =>
      refine ⟨SourceEqualityNativeDemandValidity.inputs_heap holds control state inputs.1, ?_⟩
      cases actual : step control state with
      | yielded next after =>
          exact ih next after (by simpa only [SourceEqualityNativeDemandFieldExecution.InputsThrough, actual] using inputs.2)
      | done | failed | constraintError | blocked => trivial

/-- Existing checked input plans supply the physical subchecks needed by semantic heap preservation. -/
theorem execute_semantic_of_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (control : Control Output) (state : CheckedState width)
    (semantic : SemanticReady state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandFieldExecution.InputsThrough holds fuel control state) :
    SemanticReady (execute fuel control state).state.native.machine.heap :=
  execute_semantic fuel control state semantic (physical_inputs holds fuel control state inputs)

end MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap
