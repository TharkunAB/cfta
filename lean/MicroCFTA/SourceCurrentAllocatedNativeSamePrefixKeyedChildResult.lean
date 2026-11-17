import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandNodeReadback
import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
import MicroCFTA.SourceCurrentNativeWriterReadyRetention
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Keyed child results at the same parent finish

The actual original trace supplies the child inputs and its reader suffix.
The parent finish's past cache law applies to the retained child cell.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
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

private theorem keyed_cell
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (count : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width)
    (value : Value Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (actual : Steps count (.code (requestNode request.domain request.left request.right))
      before (.code (.pure value)) after) :
    ∃ handle, after.native.nodes.cells handle = some ⟨request, .returned value⟩ := by
  have call := SourceEqualityNativeDemandNodeReadback.of_trace count request before after value actual
  cases call with
  | direct bodyCount middle result unresolved body =>
      rw [keyed] at unresolved
      cases unresolved
  | ready actualKey handle original result requested published stored =>
      have same := SourceCurrentAllocatedNativePhysicalCache.node_request_exact before.native physical
        request ready actualKey ⟨requested, safe actualKey requested⟩ handle published _ stored
      change original = request at same
      exact ⟨handle, by simpa only [same] using stored⟩
  | started bodyCount handle chosen running captured middle result selected demanded _suspended evaluating _machine body =>
      have same := SourceCurrentAllocatedNativePhysicalCache.node_started request captured before.native chosen running
        handle physical ready (safe key keyed) selected demanded
      subst captured
      have chosenShape := SourceRecursiveIntersectionNative.lookupNode_shape request before.native physical.shape
      simp only [selected] at chosenShape
      have runningShape := SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
      simp only [demanded] at runningShape
      have owner := SourceEqualityNativeDemandProtectedPrefix.node_body_owner bodyCount handle request
        ⟨running, before.operations⟩ middle value runningShape evaluating body
      exact ⟨handle, owner.2⟩

private theorem child_at_reader
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel wholeCount used childCount : Nat)
    (readerControl : Control (Value Symbol Guard)) (beforeFinish : Checked width)
    (_bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      readerControl beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : NodeRequest Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key)
    (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : Value Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    nodeLaw child value ∧ ∃ handle,
      childAfter.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        readerControl beforeFinish ∧
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
    (.code (requestNode child.domain child.left child.right)) childNext childBefore boundInputs
  change NodeReady childBefore.native.machine child ∧
    (∀ key, SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width child.domain child.left child.right) at childInputs
  obtain ⟨handle, stored⟩ := keyed_cell childCount child childBefore childAfter value key keyed
    childPhysical childInputs.1 childInputs.2 childActual
  have boundChild : Steps childCount
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore
      (.code (childNext value)) childAfter := by
    have bound := childActual.bind _ _ _ _ _ childNext
    simpa only [Control.bind, Code.bind] using bound
  obtain ⟨checkedChild, actualSuffix⟩ := checked_split outerTrace boundChild (by omega)
  have afterPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedChild childPhysical).1
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained actualSuffix afterPhysical.shape
  have currentCell := retained.nodes handle child value stored
  exact ⟨past.1 handle child value currentCell, handle, stored, currentCell, actualSuffix, retained⟩

/-- A completed keyed child uses the past cache laws at this actual parent finish. -/
theorem keyed_child_law_at_node_finish
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
    (child : NodeRequest Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key)
    (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : Value Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    nodeLaw child value ∧ ∃ handle,
      childAfter.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native := by
  exact child_at_reader nodeLaw edgeLaw rootRequest machine machineValid operations fuel wholeCount used childCount
    (.code (.finishNode parentHandle parentValue parentNext)) beforeFinish bounded whole past
    child key keyed childNext childBefore childAfter value childBound origin childActual

/-- A completed keyed child uses the past cache laws at this actual parent finish. -/
theorem keyed_child_law_at_edge_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel wholeCount used childCount : Nat)
    (parentHandle : Nat) (parentValue : EdgeValue Symbol Guard)
    (parentNext : Code Symbol Guard (Value Symbol Guard)) (beforeFinish : Checked width)
    (bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishEdge parentHandle parentValue parentNext)) beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : NodeRequest Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key)
    (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : Value Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    nodeLaw child value ∧ ∃ handle,
      childAfter.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        (.code (.finishEdge parentHandle parentValue parentNext)) beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native := by
  exact child_at_reader nodeLaw edgeLaw rootRequest machine machineValid operations fuel wholeCount used childCount
    (.code (.finishEdge parentHandle parentValue parentNext)) beforeFinish bounded whole past
    child key keyed childNext childBefore childAfter value childBound origin childActual

end MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult

namespace MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
set_option autoImplicit false

/- Note [A keyed child at an actual reader]
The private proof already accepts an arbitrary reader control.
The public finish adapters specialize that control to a parent finish.
This alias exposes the original reader contract without changing its proof.
The past Returned laws remain premises. This export supplies no admission
or NoNewMu fact by itself. The complete cold trace and child receipt stay
in the same execution, with the exact suffix and retained cell.
-/

/-- The existing keyed child proof applies at this same actual reader. -/
theorem keyed_child_law_at_actual_reader
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel wholeCount used childCount : Nat)
    (readerControl : Control (Value Symbol Guard)) (beforeFinish : Checked width)
    (_bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      readerControl beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : NodeRequest Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key)
    (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : Value Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    nodeLaw child value ∧ ∃ handle,
      childAfter.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        readerControl beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native
 := by
  exact child_at_reader (width := width) nodeLaw edgeLaw rootRequest machine machineValid operations
    fuel wholeCount used childCount readerControl beforeFinish _bounded whole past
    child key keyed childNext childBefore childAfter value childBound origin childActual

end MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult

namespace MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
set_option autoImplicit false

/- Note [Warm child reader]
The original reader proof uses cold initialization to obtain Physical.
This export starts at the actual checked state with that past fact.
The checked whole trace supplies the child inputs and the exact suffix.
The past Returned law applies to the same retained child cell.
This theorem supplies no source qualification or payload meaning.
-/

theorem keyed_child_law_at_actual_warm_reader
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (start : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)
    (fuel wholeCount used childCount : Nat)
    (readerControl : Control (Value Symbol Guard)) (beforeFinish : Checked width)
    (_bounded : wholeCount ≤ fuel)
    (whole : Trace wholeCount (.code (.node rootRequest .pure))
      start
      readerControl beforeFinish)
    (past : Returned nodeLaw beforeFinish.native.nodes ∧ Returned edgeLaw beforeFinish.native.edges)
    (child : NodeRequest Symbol Guard) (key : IntersectionFlatMemoKeyDomain.Triple width)
    (keyed : SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key)
    (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (childBefore childAfter : Checked width) (value : Value Symbol Guard)
    (childBound : used + childCount ≤ wholeCount)
    (origin : Steps used (.code (.node rootRequest .pure))
      start
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right))
      childBefore (.code (.pure value)) childAfter) :
    nodeLaw child value ∧ ∃ handle,
      childAfter.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      beforeFinish.native.nodes.cells handle = some ⟨child, .returned value⟩ ∧
      Trace (wholeCount - used - childCount) (.code (childNext value)) childAfter
        readerControl beforeFinish ∧
      SourceEqualityNativeDemandMemo.Retained childAfter.native beforeFinish.native
 := by
  have childPositive : 0 < childCount := by
    cases childCount with
    | zero => cases (steps_zero _ _ _ _ childActual).1
    | succ => omega
  obtain ⟨checkedOrigin, outerTrace⟩ := checked_split whole origin (by omega)
  have childPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedOrigin initialPhysical).1
  have boundInputs := first_inputs outerTrace (by omega)
  have childInputs := SourceCurrentAllocatedNativeSemanticTraceReadback.inputs_before_bind
    (.code (requestNode child.domain child.left child.right)) childNext childBefore boundInputs
  change NodeReady childBefore.native.machine child ∧
    (∀ key, SourceRecursiveIntersectionMemo.requestKey width child.domain child.left child.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width child.domain child.left child.right) at childInputs
  obtain ⟨handle, stored⟩ := keyed_cell childCount child childBefore childAfter value key keyed
    childPhysical childInputs.1 childInputs.2 childActual
  have boundChild : Steps childCount
      (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore
      (.code (childNext value)) childAfter := by
    have bound := childActual.bind _ _ _ _ _ childNext
    simpa only [Control.bind, Code.bind] using bound
  obtain ⟨checkedChild, actualSuffix⟩ := checked_split outerTrace boundChild (by omega)
  have afterPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension checkedChild childPhysical).1
  have retained := SourceCurrentNativeWriterReadyRetention.trace_retained actualSuffix afterPhysical.shape
  have currentCell := retained.nodes handle child value stored
  exact ⟨past.1 handle child value currentCell, handle, stored, currentCell, actualSuffix, retained⟩

end MicroCFTA.SourceCurrentAllocatedNativeSamePrefixKeyedChildResult
