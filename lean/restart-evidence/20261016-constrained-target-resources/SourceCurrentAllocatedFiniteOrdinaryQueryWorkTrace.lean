import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace

/-!
# Constructor Work in actual checked query prefixes

Each trace uses the request list observed in the actual checked prefix.
Each Work entry retains its actual initial and final constructor heaps.
Other supported instructions preserve the complete constructor heap.
The proof does not assume a completed query or a final capacity bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionKernel SourceEqualityNativeDemand
open SourceCurrentAllocatedFiniteOrdinaryWordExecution (Origins Certified)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (step_requests requestsThrough)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem lift_machine (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine = outcome.state.machine := by
  cases outcome <;> rfl

/-- One actual yielded instruction records its literal constructor Work. -/
theorem step_trace (bits : Nat) (source : Machine Symbol Guard)
    (control next : Control A) (before after : Checked (bits + 2))
    (certificate : Certified bits source control) (one : step control before = .yielded next after) :
    Trace before.native.machine.heap after.native.machine.heap (step_requests control before) := by
  cases control with
  | edgeBody request resume =>
      have same := SourceEqualityNativeDemandOperations.body_native request resume before
      rw [show body request resume before = .yielded next after from one] at same
      have heap := congrArg (fun native => native.machine.heap) same
      change after.native.machine.heap = before.native.machine.heap at heap
      rw [heap]
      exact .refl _
  | code code =>
      cases code with
      | pure | fail => cases one
      | enter | read | optionalBinder => cases certificate
      | work job resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact .work _ job
      | finishNode handle value rest | finishEdge handle value rest =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact .refl _
      | node request resume =>
          have same : (step (.code (.node request resume)) before).state.native.machine = before.native.machine := by
            change (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request resume) before.native)).state.native.machine = before.native.machine
            rw [lift_machine, SourceRecursiveIntersectionNative.node_step_machine]
          rw [one] at same
          have heap := congrArg (fun machine => machine.heap) same
          change after.native.machine.heap = before.native.machine.heap at heap
          rw [heap]
          exact .refl _
      | edge request resume =>
          have same : (step (.code (.edge request resume)) before).state.native.machine = before.native.machine := by
            cases selected : SourceRecursiveIntersectionThunks.lookupEdge (bits + 2) request before.native with
            | mk handle chosen =>
                have chosenMachine : chosen.machine = before.native.machine := by
                  simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
                cases demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen with
                | mk observation running =>
                    have runningMachine : running.machine = chosen.machine := by
                      simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
                    cases observation <;> simpa only [step, selected, demanded, Outcome.state] using runningMachine.trans chosenMachine
          rw [one] at same
          have heap := congrArg (fun machine => machine.heap) same
          change after.native.machine.heap = before.native.machine.heap at heap
          rw [heap]
          exact .refl _

/-- Every actual yielded prefix has the same ordered constructor Work trace. -/
theorem «prefix» (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (actual : Steps fuel control before next after) :
    Trace before.native.machine.heap after.native.machine.heap (requestsThrough fuel control before) := by
  induction actual with
  | refl => exact .refl _
  | cons control before middle current next after count one rest ih =>
      have entered := SourceCurrentAllocatedFiniteOrdinaryWordExecution.step_preserves bits source valid
        control middle before current origins certificate one
      have first := step_trace bits source control middle before current certificate one
      have tail := ih entered.1 entered.2
      simpa only [requestsThrough, one] using first.trans tail

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryWorkTrace
