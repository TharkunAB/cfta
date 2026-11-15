import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
import MicroCFTA.SourceCurrentNativeWriterReadyRetention
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Edge child results at the same node-parent finish

The actual original trace supplies the child inputs and its reader suffix.
The parent finish's past cache law applies to the retained child cell.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSamePrefixEdgeChildResult
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat} {Output : Type}

set_option autoImplicit false

private theorem checked_split
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {wholeCount prefixCount : Nat} {initial middle final : Control Output}
    {start current reader : Checked width}
    (whole : Trace wholeCount initial start final reader)
    (prefixActual : Steps prefixCount initial start middle current)
    (bounded : prefixCount ≤ wholeCount) :
    Trace prefixCount initial start middle current ∧
      Trace (wholeCount - prefixCount) middle current final reader := by
  induction prefixActual generalizing wholeCount final reader with
  | refl => exact ⟨.refl _ _, by simpa only [Nat.sub_zero] using whole⟩
  | cons control state next reached middle current count one tail ih =>
      cases whole with
      | refl => omega
      | cons _ _ other advanced _ _ remaining inputs first rest =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans first)
          obtain ⟨checkedPrefix, checkedSuffix⟩ := ih rest (by omega)
          refine ⟨.cons control state next reached middle current count inputs one checkedPrefix, ?_⟩
          have lengthEq : remaining + 1 - (count + 1) = remaining - count := by omega
          simpa only [lengthEq] using checkedSuffix

private theorem first_inputs
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {control final : Control Output} {before after : Checked width}
    (actual : Trace count control before final after) (positive : 0 < count) : Inputs control before := by
  cases actual with
  | refl => omega
  | cons _ _ _ _ _ _ _ inputs _ _ => exact inputs

private theorem edge_cell
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (actual : Steps count (.code (requestEdge request.domain request.left request.right))
      before (.code (.pure value)) after) :
    ∃ handle, after.native.edges.cells handle = some ⟨request, .returned value⟩ := by
  cases count with
  | zero => cases (steps_zero _ _ _ _ actual).1
  | succ count =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ count _ _ _ _ actual
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
        cases demanded : demandEdge handle chosen with
        | mk observation running =>
          cases observation with
          | absent | busy =>
              simp only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded] at one
              cases one
          | ready result =>
              have same := Outcome.yielded.inj (by
                simpa only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded] using one)
              obtain ⟨rfl, rfl⟩ := same
              have pure := pure_trace count result value ⟨running, before.operations⟩ after tail
              have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request
                before.native chosen running handle result physical ready safe selected demanded
              have stored : running.edges.cells handle = some ⟨request, .returned result⟩ := by
                simpa only [receipt.2.1] using receipt.1
              refine ⟨handle, ?_⟩
              rw [← pure.2.2]
              simpa only [pure.2.1] using stored
          | evaluate captured =>
              have requestSame := SourceCurrentAllocatedNativePhysicalCache.edge_started request captured
                before.native chosen running handle physical ready safe selected demanded
              subst captured
              have same := Outcome.yielded.inj (by
                simpa only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded] using one)
              obtain ⟨rfl, rfl⟩ := same
              let first : Checked width := ⟨running, before.operations⟩
              let frame : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
                fun result => .finishEdge handle result (.pure result)
              obtain ⟨bodyCount, frameCount, result, middle, _total, bodyTrace, frameTrace⟩ :=
                steps_bind_inverse count (.edgeBody request .pure) frame first after value tail
              obtain ⟨remaining, _frameTotal, finalTrace⟩ :=
                SourceEqualityNativeDemandRunning.finish_edge_trace frameCount handle result (.pure result)
                  middle after value frameTrace
              have pure := pure_trace remaining result value _ after finalTrace
              have chosenShape := SourceRecursiveIntersectionNative.lookupEdge_shape request before.native physical.shape
              simp only [selected] at chosenShape
              have runningShape := SourceRecursiveIntersectionNative.demandEdge_shape handle chosen chosenShape
              simp only [demanded] at runningShape
              have started := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running request demanded).2
              have owner := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner bodyCount handle request
                first middle result runningShape started bodyTrace
              refine ⟨handle, ?_⟩
              rw [← pure.2.2]
              simpa only [pure.2.1] using owner.2


private theorem child_at_parent
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel wholeCount used childCount : Nat)
    (parentHandle : Nat) (parentValue : Value Symbol Guard)
    (parentNext : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (_bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : EdgeRequest Symbol Guard)
    (childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : EdgeValue Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestEdge child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    edgeLaw child value ∧ ∃ handle,
      childAfter.native.edges.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.edges.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native := by
  have childPositive : 0 < childCount := by
    cases childCount with
    | zero => cases (steps_zero _ _ _ _ childActual).1
    | succ => omega
  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  obtain ⟨checkedOrigin, outerTrace⟩ := checked_split whole origin (by omega)
  have childPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedOrigin initialPhysical).1
  have boundInputs := first_inputs outerTrace (by omega)
  have childInputs := SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind
    (.code (requestEdge child.domain child.left child.right)) childNext childBefore boundInputs
  change EdgeReady childBefore.native.machine child ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width child.domain child.left child.right at childInputs
  obtain ⟨handle, stored⟩ := edge_cell childCount child childBefore childAfter value
    childPhysical childInputs.1 childInputs.2 childActual
  have boundChild : Steps childCount
      (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore
      (.code (childNext value)) childAfter := by
    have bound := childActual.bind _ _ _ _ _ childNext
    simpa only [Control.bind, Code.bind] using bound
  obtain ⟨checkedChild, actualSuffix⟩ := checked_split outerTrace boundChild (by omega)
  have afterPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedChild childPhysical).1
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained actualSuffix afterPhysical.shape
  have currentCell := retained.edges handle child value stored
  exact ⟨past.2 handle child value currentCell, handle, stored, currentCell, actualSuffix, retained⟩

/-- An actual completed edge child uses the past cache laws at this same node-parent finish. -/
theorem edge_child_law_at_node_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel wholeCount used childCount : Nat)
    (parentHandle : Nat) (parentValue : Value Symbol Guard)
    (parentNext : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : EdgeRequest Symbol Guard)
    (childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : EdgeValue Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestEdge child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    edgeLaw child value ∧ ∃ handle,
      childAfter.native.edges.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.edges.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native := by
  exact child_at_parent nodeLaw edgeLaw rootRequest machine machineValid operations fuel wholeCount used childCount
    parentHandle parentValue parentNext beforeFinish bounded whole past child childNext childBefore childAfter value
    childBound origin childActual

end MicroCFTA.SourceCurrentAllocatedNativeSamePrefixEdgeChildResult
