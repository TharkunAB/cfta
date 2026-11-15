import MicroCFTA.SourceCurrentAllocatedNativeNodeReturnOrigin
import MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin

/-!
# Actual compiled origins of current returned node cells

One receipt joins the actual compiled body to its finish and the observed
endpoint. The original query starts both native memo families empty.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeCompiledReturnOrigin
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

/-- Every current returned node has a compiled writer in this original initial-query execution. -/
theorem returned_node_cell_compiled_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (rest : Control (Value Symbol Guard)) (after : Checked width) (fuel count : Nat)
    (bounded : count ≤ fuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width) rest after)
    (handle : Nat) (captured : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (stored : after.native.nodes.cells handle = some ⟨captured, .returned value⟩) :
    ∃ (dispatchUsed bodyCount suffixCount : Nat) (beforeBody beforeFinish : Checked width)
      (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      dispatchUsed + bodyCount + 1 + suffixCount = count ∧
      0 < dispatchUsed ∧ dispatchUsed < fuel ∧ bodyCount < fuel ∧
      Steps dispatchUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code ((compileNode captured).bind
          (fun result => .finishNode handle result (resume result)))) beforeBody ∧
      beforeBody.native.nodes.cells handle = some ⟨captured, .evaluating⟩ ∧
      Steps bodyCount (.code (compileNode captured)) beforeBody (.code (.pure value)) beforeFinish ∧
      beforeFinish.native.nodes.cells handle = some ⟨captured, .evaluating⟩ ∧
      Trace (dispatchUsed + bodyCount) (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code (.finishNode handle value (resume value))) beforeFinish ∧
      Trace 1 (.code (.finishNode handle value (resume value))) beforeFinish (.code (resume value))
        {beforeFinish with native := SourceRecursiveIntersectionThunks.finishNode handle value beforeFinish.native} ∧
      ({beforeFinish with native := SourceRecursiveIntersectionThunks.finishNode handle value beforeFinish.native} : Checked width).native.nodes.cells
        handle = some ⟨captured, .returned value⟩ ∧
      Trace suffixCount (.code (resume value))
        {beforeFinish with native := SourceRecursiveIntersectionThunks.finishNode handle value beforeFinish.native}
        rest after := by
  obtain ⟨finishUsed, suffixCount, beforeFinish, next, total, _, finishBound,
      finishPrefix, finishOwner, oneFinish, finished, suffixActual⟩ :=
    SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_finish_prefix
      machine operations (.code (.node rootRequest .pure)) rest after fuel count bounded actual
      handle captured value stored
  obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, bodyTotal, positive, dispatchBound,
      dispatchPrefix, bodyOwner, rawBody, continuation⟩ :=
    SourceCurrentAllocatedNativeCompileDispatchOrigin.compiled_node_origin_from_initial_query_finish
      rootRequest machine machineValid operations fuel finishUsed handle captured value next beforeFinish
      finishBound finishPrefix finishOwner
  refine ⟨dispatchUsed, bodyCount, suffixCount, beforeBody, beforeFinish, resume,
    by omega, positive, dispatchBound, by omega, dispatchPrefix, bodyOwner, rawBody, finishOwner,
    ?_, ?_, finished, ?_⟩
  · simpa only [bodyTotal, continuation] using finishPrefix
  · simpa only [continuation] using oneFinish
  · simpa only [continuation] using suffixActual

end MicroCFTA.SourceCurrentAllocatedNativeNodeCompiledReturnOrigin
