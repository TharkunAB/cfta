import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryWordExecution

/-!
# Constructor reservations in actual native query prefixes

The count follows each actual Work request and its initial cache lookup.
The observation does not subtract final counters from initial counters.
Every finite yielded prefix retains the exact two reservation equations.
A completed query or root execution is not an input to this count.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryReservations
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionKernel SourceEqualityNativeDemand
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryWordExecution (Origins Certified)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Requests" => List (Request Symbol Guard)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Only the current literal Work instruction issues constructor requests in this fragment. -/
def step_requests (control : Control A) (before : Checked width) : Requests :=
  match control with
  | .code (.work job _) => observe job before.native.machine.heap
  | _ => []

/-- Observe constructor requests in a bounded actual instruction prefix. -/
noncomputable def requestsThrough : Nat → Control A → Checked width → Requests
  | 0, _, _ => []
  | fuel + 1, control, before => step_requests control before ++
      match step control before with
      | .yielded next after => requestsThrough fuel next after
      | _ => []

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem counts_append (first rest : Requests) :
    nodeReservations (first ++ rest) = nodeReservations first + nodeReservations rest ∧
    edgeReservations (first ++ rest) = edgeReservations first + edgeReservations rest := by
  induction first with
  | nil => simp [nodeReservations, edgeReservations]
  | cons request first ih =>
      cases request with
      | node key miss => cases miss <;> simp_all [nodeReservations, edgeReservations] <;> omega
      | edge key miss => cases miss <;> simp_all [nodeReservations, edgeReservations] <;> omega

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem lift_machine (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine = outcome.state.machine := by
  cases outcome <;> rfl

/-- Each actual yielded instruction increments only the reservations in its observed Work requests. -/
theorem step_counts (bits : Nat) (source : Machine Symbol Guard)
    (control next : Control A) (before after : Checked (bits + 2))
    (certificate : Certified bits source control) (one : step control before = .yielded next after) :
    after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next + nodeReservations (step_requests control before) ∧
    after.native.machine.heap.edges.next = before.native.machine.heap.edges.next + edgeReservations (step_requests control before) := by
  cases control with
  | edgeBody request resume =>
      have same := SourceEqualityNativeDemandOperations.body_native request resume before
      rw [show body request resume before = .yielded next after from one] at same
      exact ⟨congrArg (fun native => native.machine.heap.nodes.next) same,
        congrArg (fun native => native.machine.heap.edges.next) same⟩
  | code code =>
      cases code with
      | pure | fail => cases one
      | enter | read | optionalBinder => cases certificate
      | work job resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact run_next job before.native.machine.heap
      | finishNode handle value rest | finishEdge handle value rest =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨rfl, rfl⟩
      | node request resume =>
          have same : (step (.code (.node request resume)) before).state.native.machine = before.native.machine := by
            change (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request resume) before.native)).state.native.machine = before.native.machine
            rw [lift_machine, SourceRecursiveIntersectionNative.node_step_machine]
          rw [one] at same
          exact ⟨congrArg (fun machine => machine.heap.nodes.next) same,
            congrArg (fun machine => machine.heap.edges.next) same⟩
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
          exact ⟨congrArg (fun machine => machine.heap.nodes.next) same,
            congrArg (fun machine => machine.heap.edges.next) same⟩

/-- Raw finite yielded prefixes give exact reservation equations without a completed receipt. -/
theorem prefix_counts (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (actual : Steps fuel control before next after) :
    after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next + nodeReservations (requestsThrough fuel control before) ∧
    after.native.machine.heap.edges.next = before.native.machine.heap.edges.next + edgeReservations (requestsThrough fuel control before) := by
  induction actual with
  | refl => simp [requestsThrough, nodeReservations, edgeReservations]
  | cons control before middle current next after count one rest ih =>
      have entered := SourceCurrentAllocatedFiniteOrdinaryWordExecution.step_preserves bits source valid
        control middle before current origins certificate one
      have first := step_counts bits source control middle before current certificate one
      have tail := ih entered.1 entered.2
      have summed := counts_append (step_requests control before) (requestsThrough count middle current)
      simp only [requestsThrough, one] at *
      omega

/-- The number of actual executed requests bounds both supplies at any yielded prefix. -/
theorem prefix_bounds (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (actual : Steps fuel control before next after) :
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeRequests (requestsThrough fuel control before) ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeRequests (requestsThrough fuel control before) := by
  have counted := prefix_counts bits source valid fuel control next before after origins certificate actual
  have bounded := reservations_le_requests (requestsThrough fuel control before)
  omega

/-- Initial supply plus an actual prefix request budget derives numeric capacity at that entry. -/
theorem capacity_after (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2))
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (actual : Steps fuel control before next after)
    (nodes : before.native.machine.heap.nodes.next + nodeRequests (requestsThrough fuel control before) ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeRequests (requestsThrough fuel control before) ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after := by
  have bounded := prefix_bounds bits source valid fuel control next before after origins certificate actual
  exact ⟨Nat.le_trans bounded.1 nodes, Nat.le_trans bounded.2 edges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryReservations
