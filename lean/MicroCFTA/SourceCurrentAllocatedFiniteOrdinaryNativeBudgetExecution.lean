import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryQueryReservations

/-!
# Constructor budgets through actual yielded native prefixes

The remaining source code carries a constructor request budget.
Each literal Work action consumes its own observed request count.
Memo hits skip their producer budget. Starts use the captured owner.
Every finite yielded prefix stays within the initial code budget.
No completed query or bound on its actual request list is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode (Scheme Bound ControlBound)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (step_requests requestsThrough)
open SourceCurrentAllocatedFiniteOrdinaryWordExecution (Origins Certified)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WNode" => SourceCurrentAllocatedFiniteOrdinaryWordCode.NodeInputs
local notation "WEdge" => SourceCurrentAllocatedFiniteOrdinaryWordCode.EdgeInputs
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem node_ready (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard)
    (inputs : WNode bits source request) : NodeReady source request := by
  refine ⟨?_, inputs.2.2.2.1, inputs.2.2.2.2⟩
  rw [inputs.1]
  exact SourceRecursiveIntersectionKernel.empty_domain source

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_ready (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard)
    (inputs : WEdge bits source request) : EdgeReady source request := by
  refine ⟨?_, inputs.2.2.2.1, inputs.2.2.2.2⟩
  rw [inputs.1]
  exact SourceRecursiveIntersectionKernel.empty_domain source

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem node_safe (bits : Nat) (source : Machine Symbol Guard) (request : NodeRequest Symbol Guard)
    (inputs : WNode bits source request) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  rw [inputs.1]
  exact SourceCurrentAllocatedFiniteOrdinaryKeys.node_key_safe_empty inputs.2.1 inputs.2.2.1

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_safe (bits : Nat) (source : Machine Symbol Guard) (request : EdgeRequest Symbol Guard)
    (inputs : WEdge bits source request) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  rw [inputs.1]
  exact SourceCurrentAllocatedFiniteOrdinaryKeys.edge_key_safe_empty inputs.2.1 inputs.2.2.1

variable (scheme : Scheme Symbol Guard)
variable (compiled : ∀ request, scheme.nodeInputs request → Bound scheme (compileNode request) (scheme.nodeCost request))
variable (bodyBound : ∀ {A : Type} (request : EdgeRequest Symbol Guard)
    (resume : EdgeValue Symbol Guard → Code Symbol Guard A) {width : Nat}
    (before after : Checked width) (next : Control A) (tail : Nat),
    scheme.edgeInputs request → (∀ value, Bound scheme (resume value) tail) →
    body request resume before = .yielded next after → ControlBound scheme next (scheme.edgeCost request + tail))

include compiled bodyBound in
/-- One yielded instruction consumes only its literal Work requests from the current source budget. -/
theorem step_bound (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (control next : Control A) (before after : Checked (bits + 2)) (budget : Nat)
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (bounded : ControlBound scheme control budget) (one : step control before = .yielded next after) :
    ∃ remaining, ControlBound scheme next remaining ∧
      nodeRequests (step_requests control before) + edgeRequests (step_requests control before) + remaining ≤ budget := by
  cases control with
  | edgeBody request resume =>
      obtain ⟨inputs, tail, enough, rest⟩ := bounded
      exact ⟨scheme.edgeCost request + tail, bodyBound request resume before after next tail inputs rest one, by
        simpa only [step_requests, nodeRequests, edgeRequests, Nat.zero_add] using enough⟩
  | code code =>
      cases code with
      | pure | fail => simp only [step, SourceRecursiveIntersectionNative.step, lift] at one; cases one
      | enter | read | optionalBinder => cases bounded
      | work job resume =>
          obtain ⟨own, tail, enough, observed, rest⟩ := bounded
          have counts := observed before.native.machine.heap
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨tail, rest _, by simpa only [step_requests] using Nat.le_trans (Nat.add_le_add_right counts tail) enough⟩
      | finishNode handle value rest | finishEdge handle value rest =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact ⟨budget, bounded, by simp only [step_requests, nodeRequests, edgeRequests, Nat.zero_add, Nat.le_refl]⟩
      | node request resume =>
          obtain ⟨inputs, tail, enough, rest⟩ := bounded
          have ready := node_ready bits source request certificate.1
          have safe := node_safe bits source request certificate.1
          cases selected : SourceRecursiveIntersectionThunks.lookupNode (bits + 2) request before.native with
          | mk selection chosen =>
              cases selection with
              | direct actual =>
                  obtain ⟨same, unchanged⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected
                  subst actual
                  subst chosen
                  simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] at one
                  cases one
                  refine ⟨scheme.nodeCost request + tail, ?_, ?_⟩
                  · exact Bound.bind (compiled request inputs) rest
                  · simpa only [step_requests, nodeRequests, edgeRequests, Nat.zero_add] using enough
              | memoized handle =>
                  cases demanded : SourceRecursiveIntersectionThunks.demandNode handle chosen with
                  | mk observation running =>
                      cases observation with
                      | absent | busy => simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one; cases one
                      | ready value =>
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          exact ⟨tail, rest value, by
                            simp only [step_requests, nodeRequests, edgeRequests, Nat.zero_add]
                            omega⟩
                      | evaluate actual =>
                          have same := origins.node_started source valid request actual before.native chosen running handle ready safe selected demanded
                          subst actual
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          refine ⟨scheme.nodeCost request + tail, ?_, ?_⟩
                          · exact Bound.bind (compiled request inputs) (fun value => rest value)
                          · simpa only [step_requests, nodeRequests, edgeRequests, Nat.zero_add] using enough
      | edge request resume =>
          obtain ⟨inputs, tail, enough, rest⟩ := bounded
          have ready := edge_ready bits source request certificate.1
          have safe := edge_safe bits source request certificate.1
          cases selected : SourceRecursiveIntersectionThunks.lookupEdge (bits + 2) request before.native with
          | mk handle chosen =>
              cases demanded : SourceRecursiveIntersectionThunks.demandEdge handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy => simp only [step, selected, demanded] at one; cases one
                  | ready value =>
                      simp only [step, selected, demanded] at one
                      cases one
                      exact ⟨tail, rest value, by
                        simp only [step_requests, nodeRequests, edgeRequests, Nat.zero_add]
                        omega⟩
                  | evaluate actual =>
                      have same := origins.edge_started source valid request actual before.native chosen running handle ready safe selected demanded
                      subst actual
                      simp only [step, selected, demanded] at one
                      cases one
                      exact ⟨budget, ⟨inputs, tail, enough, fun value => rest value⟩, by
                        simp only [step_requests, nodeRequests, edgeRequests, Nat.zero_add, Nat.le_refl]⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem requests_append (first rest : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) :
    nodeRequests (first ++ rest) = nodeRequests first + nodeRequests rest ∧
    edgeRequests (first ++ rest) = edgeRequests first + edgeRequests rest := by
  induction first with
  | nil => simp [nodeRequests, edgeRequests]
  | cons request first ih => cases request <;> simp_all [nodeRequests, edgeRequests] <;> omega

include compiled bodyBound in
/-- Every finite actual prefix stays within an initial constructor budget computed for its code. -/
theorem prefix_bound (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2)) (budget : Nat)
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (bounded : ControlBound scheme control budget) (actual : Steps fuel control before next after) :
    ∃ remaining, ControlBound scheme next remaining ∧
      nodeRequests (requestsThrough fuel control before) + edgeRequests (requestsThrough fuel control before) + remaining ≤ budget := by
  induction actual generalizing budget with
  | refl => exact ⟨budget, bounded, by simp [requestsThrough, nodeRequests, edgeRequests]⟩
  | cons control before middle current next after count one rest ih =>
      obtain ⟨currentBudget, currentBound, spent⟩ :=
        step_bound scheme compiled bodyBound bits source valid control middle before current budget origins certificate bounded one
      have preserved := SourceCurrentAllocatedFiniteOrdinaryWordExecution.step_preserves bits source valid
        control middle before current origins certificate one
      obtain ⟨remaining, finalBound, tail⟩ := ih currentBudget preserved.1 preserved.2 currentBound
      have appended := requests_append (step_requests control before) (requestsThrough count middle current)
      refine ⟨remaining, finalBound, ?_⟩
      simp only [requestsThrough, one]
      omega

include compiled bodyBound in
/-- The static source budget bounds both actual constructor supplies at every yielded prefix. -/
theorem prefix_supplies (bits : Nat) (source : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid source)
    (fuel : Nat) (control next : Control A) (before after : Checked (bits + 2)) (budget : Nat)
    (origins : Origins source before.native) (certificate : Certified bits source control)
    (bounded : ControlBound scheme control budget) (actual : Steps fuel control before next after) :
    after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + budget ∧
    after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + budget := by
  obtain ⟨remaining, finalBound, spent⟩ := prefix_bound scheme compiled bodyBound bits source valid fuel control next
    before after budget origins certificate bounded actual
  have reserved := SourceCurrentAllocatedFiniteOrdinaryQueryReservations.prefix_bounds bits source valid fuel control next
    before after origins certificate actual
  omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetExecution
