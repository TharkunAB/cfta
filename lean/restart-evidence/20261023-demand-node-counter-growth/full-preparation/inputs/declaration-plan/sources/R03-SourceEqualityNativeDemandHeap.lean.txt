import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceRecursiveIntersectionNativePrefixCoverage

/-!
# Heap preservation for actual checked native demand

Each current constructor instruction checks its physical arguments in the
current heap. Memo instructions and checked edge bodies leave that heap
unchanged. Finite execution derives heap preservation from these current
checks on the actual reached path. No future heap invariant is assumed.
-/
namespace MicroCFTA.SourceEqualityNativeDemandHeap
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityRequiredCache (Ready Keeps)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Only physical constructors and optional binders require current heap input checks. -/
def Inputs : Control Output → State width → Prop
  | .code (.work job _), state => WorkInputs state.native.machine.heap job
  | .code (.optionalBinder _ body _), state => InternedProbeProvenance.Available state.native.machine.heap body
  | _, _ => True

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- Actual edge publication and demand leave the physical constructor heap unchanged. -/
theorem step_edge_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) :
    (step (.code (.edge request next)) state).state.native.machine.heap = state.native.machine.heap := by
  cases lookup : lookupEdge width request state.native with
  | mk handle chosen =>
      have chosenMachine : chosen.machine = state.native.machine := by
        simpa only [lookup] using SourceRecursiveIntersectionNative.lookupEdge_machine request state.native
      cases demand : demandEdge handle chosen with
      | mk observation current =>
          have currentMachine : current.machine = chosen.machine := by
            simpa only [demand] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
          cases observation <;> simpa only [step, lookup, demand, Outcome.state] using
            congrArg (fun machine => machine.heap) (currentMachine.trans chosenMachine)

/-- Checked edge bodies retain heap readiness and both physical histories on every outcome. -/
theorem body_keeps (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (ready : Ready state.native.machine.heap) :
    Keeps state.native.machine.heap (body request next state).state.native.machine.heap := by
  rw [SourceEqualityNativeDemandOperations.body_native]
  exact SourceEqualityRequiredCache.pure_keeps _ ready

/-- Current physical input checks derive complete heap preservation for every actual step outcome. -/
theorem step_keeps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : State width) (ready : Ready state.native.machine.heap)
    (inputs : Inputs control state) :
    Keeps state.native.machine.heap (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next => exact body_keeps request next state ready
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge =>
          exact SourceEqualityRequiredCache.pure_keeps _ ready
      | work job next =>
          change Keeps state.native.machine.heap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact SourceEqualityNativeDemandHeapPrimitives.work_keeps job state.native.machine.heap ready inputs
      | optionalBinder pair body next =>
          obtain ⟨value, after, done, keeps, _⟩ := SourceEqualityNativeDemandHeapPrimitives.optionalBinder_complete
            pair body state.native.machine.heap ready inputs
          simpa only [step, SourceRecursiveIntersectionNative.step, done, lift, Outcome.state, advance] using keeps
      | node request next =>
          change Keeps state.native.machine.heap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact SourceEqualityRequiredCache.pure_keeps _ ready
      | edge request next =>
          rw [step_edge_heap]
          exact SourceEqualityRequiredCache.pure_keeps _ ready

/-- Physical input checks are required only along the actual reached control path. -/
noncomputable def InputsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → State width → Prop
  | 0, control, state => Inputs control state
  | fuel + 1, control, state =>
      Inputs control state ∧ match step control state with
      | .yielded next after => InputsThrough fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- Every finite actual native execution retains its ready heap and both physical histories. -/
theorem execute_keeps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : State width) (ready : Ready state.native.machine.heap)
    (inputs : InputsThrough fuel control state) :
    Keeps state.native.machine.heap (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact SourceEqualityRequiredCache.pure_keeps _ ready
  | succ fuel ih =>
      have one := step_keeps control state ready inputs.1
      cases observed : step control state with
      | yielded next after =>
          have nextInputs : InputsThrough fuel next after := by simpa only [observed] using inputs.2
          have checked : Keeps state.native.machine.heap after.native.machine.heap := by
            simpa only [observed, Outcome.state] using one
          have rest := ih next after checked.ready nextInputs
          simpa only [execute, observed] using checked.trans rest
      | done | failed | constraintError | blocked =>
          simpa only [execute, observed, Outcome.state] using one

end MicroCFTA.SourceEqualityNativeDemandHeap
