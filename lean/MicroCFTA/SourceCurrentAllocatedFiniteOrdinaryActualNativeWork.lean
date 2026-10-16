import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources

/-!
# Constructor Work from supplied physical native traces

Each physical instruction supplies its own current input and word checks.
Those checks retain the complete captured owner at a memo start.
The source-code potential bounds the same actual Work trace.
No constructor capacity or reserved headroom is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualNativeWork
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode (Scheme Bound ControlBound)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryQueryReservations (step_requests requestsThrough)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WorkTrace" => SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem selected_node_safe
    (request : NodeRequest Symbol Guard) (before chosen : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen)) :
    SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right := by
  cases keyEq : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simp only [lookupNode, keyEq] at selected; cases selected
  | some key => exact safe key keyEq

variable (scheme : Scheme Symbol Guard)
variable (compiled : ∀ request, scheme.nodeInputs request → Bound scheme (compileNode request) (scheme.nodeCost request))
variable (bodyBound : ∀ {A : Type} (request : EdgeRequest Symbol Guard)
    (resume : EdgeValue Symbol Guard → Code Symbol Guard A) {width : Nat}
    (before after : Checked width) (next : Control A) (tail : Nat),
    scheme.edgeInputs request → (∀ value, Bound scheme (resume value) tail) →
    body request resume before = .yielded next after → ControlBound scheme next (scheme.edgeCost request + tail))

include compiled bodyBound in
/-- One yielded instruction consumes only its literal Work requests from the current source budget. -/
theorem step_bound (control next : Control A) (before after : Checked width) (budget : Nat)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (physical : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
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
          cases selected : SourceRecursiveIntersectionThunks.lookupNode width request before.native with
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
                          have safe := selected_node_safe request before.native chosen handle physical.2 selected
                          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before.native chosen running
                            handle valid physical.1 safe selected demanded
                          subst actual
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          refine ⟨scheme.nodeCost request + tail, ?_, ?_⟩
                          · exact Bound.bind (compiled request inputs) (fun value => rest value)
                          · simpa only [step_requests, nodeRequests, edgeRequests, Nat.zero_add] using enough
      | edge request resume =>
          obtain ⟨inputs, tail, enough, rest⟩ := bounded
          cases selected : SourceRecursiveIntersectionThunks.lookupEdge width request before.native with
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
                      have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before.native chosen running
                        handle valid physical.1 physical.2 selected demanded
                      subst actual
                      simp only [step, selected, demanded] at one
                      cases one
                      exact ⟨budget, ⟨inputs, tail, enough, fun value => rest value⟩, by
                        simp only [step_requests, nodeRequests, edgeRequests, Nat.zero_add, Nat.le_refl]⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem lift_machine (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine = outcome.state.machine := by
  cases outcome <;> rfl

/-- One actual yielded instruction records its literal constructor Work. -/
private theorem step_work (control next : Control A) (before after : Checked width)
    (budget : Nat) (bounded : ControlBound scheme control budget) (one : step control before = .yielded next after) :
    WorkTrace before.native.machine.heap after.native.machine.heap (step_requests control before) := by
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
      | enter | read | optionalBinder => cases bounded
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
            cases selected : SourceRecursiveIntersectionThunks.lookupEdge width request before.native with
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

include compiled bodyBound in
/-- A supplied actual prefix spends only its initial source-code potential. -/
theorem prefix_bound (fuel : Nat) (control next : Control A) (before after : Checked width) (budget : Nat)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (bounded : ControlBound scheme control budget) (actual : Trace fuel control before next after) :
    ∃ remaining, ControlBound scheme next remaining ∧
      nodeRequests (requestsThrough fuel control before) + edgeRequests (requestsThrough fuel control before) + remaining ≤ budget ∧
      WorkTrace before.native.machine.heap after.native.machine.heap (requestsThrough fuel control before) := by
  induction actual generalizing budget with
  | refl => exact ⟨budget, bounded, by simp [requestsThrough, nodeRequests, edgeRequests], .refl _⟩
  | cons control before middle current next after count physical one rest ih =>
      obtain ⟨currentBudget, currentBound, spent⟩ :=
        step_bound scheme compiled bodyBound control middle before current budget valid physical bounded one
      have advanced : SourceCurrentAllocatedNativePhysicalCache.Valid current.native := by
        simpa only [one, Outcome.state] using SourceCurrentAllocatedNativePhysicalExecution.step_valid control before valid physical
      obtain ⟨remaining, finalBound, tail, later⟩ := ih currentBudget advanced currentBound
      have appendedNodes := SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.nodeRequests_append
        (step_requests control before) (requestsThrough count middle current)
      have appendedEdges := SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.edgeRequests_append
        (step_requests control before) (requestsThrough count middle current)
      refine ⟨remaining, finalBound, ?_, ?_⟩
      · simp only [requestsThrough, one]
        omega
      · simpa only [requestsThrough, one] using
          (step_work scheme control middle before current budget bounded one).trans later

/-- Actual query checks bound its exact Work without reserving either constructor supply. -/
theorem counted (rows arity bound : Nat) {left right value : Value Symbol Guard}
    {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before value after)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (stored : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (outputStored : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (leftShape : NodeShape rows arity left) (rightShape : NodeShape rows arity right)
    (heights : max (MergedOrdinaryHeight.height left) (MergedOrdinaryHeight.height right) ≤ bound) :
    SourceCurrentAllocatedFiniteOrdinaryStored.Stored after.native ∧
      SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored after.native ∧
      NodeShape (rows * rows) (max arity 1) value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height right ∧
      ∃ requests, WorkTrace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests + edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget rows arity bound ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget rows arity bound ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget rows arity bound := by
  cases actual with
  | @run fuel trace =>
      have structural := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
        ⟨emptyDomain, left, right⟩ before after fuel value trace ready.good ready.semantic stored
        ⟨rfl, NodeShape.domain left leftShape, NodeShape.domain right rightShape⟩
      have output := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
        ⟨emptyDomain, left, right⟩ before after fuel value trace ready.good ready.semantic outputStored
        rfl rows arity leftShape rightShape
      have bounded := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.request_node rows arity
        ⟨emptyDomain, left, right⟩ ⟨rfl, leftShape, rightShape⟩
      obtain ⟨remaining, _finalBound, spent, work⟩ := prefix_bound
        (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.scheme rows arity)
        (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.node_bound rows arity)
        (fun {_A} request resume {_width} before after next tail inputs continuation one =>
          SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.body_bound rows arity request inputs resume before after next tail continuation one)
        fuel (.code (requestNode emptyDomain left right)) (.code (.pure value)) before after
        (SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.nodeCost rows arity ⟨emptyDomain, left, right⟩)
        ready.good.native bounded trace
      have uniform := SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.node_mono rows arity heights
      have supplies := work.next_le
      exact ⟨structural.1, output.1, output.2, structural.2.2.1, structural.2.2.2,
        requestsThrough fuel (.code (requestNode emptyDomain left right)) before, work,
        by dsimp only [SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.nodeCost] at spent; omega,
        by dsimp only [SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.nodeCost] at spent; omega,
        by dsimp only [SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.nodeCost] at spent; omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualNativeWork
