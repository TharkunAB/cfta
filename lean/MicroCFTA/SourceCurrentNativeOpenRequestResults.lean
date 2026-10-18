import MicroCFTA.SourceCurrentAllocatedNativeRequestResults
import MicroCFTA.SourceCurrentNativeRowKeyable

/-!
# Available results of actual open native requests

A keyed hit reads an available value from the actual native cell.
A keyed miss checks its returned value in the actual finish frame.
A successful unkeyed request returns Empty.
-/
namespace MicroCFTA.SourceCurrentNativeOpenRequestResults
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse)
open SourceCurrentAllocatedNativeRequestResults (finish_node_result)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

private theorem keyed_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Available after.native.machine.heap value := by
  cases trace with
  | cons _ _ next current _ _ rest inputs one tail =>
      have chosenValid := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid before.native valid request
        inputs.1 (inputs.2 key requested)
      cases selected : lookupNode width request before.native with
      | mk selection chosen =>
          simp only [selected] at chosenValid
          cases selection with
          | direct actual =>
              simp only [lookupNode, requested] at selected
              cases selected
          | memoized handle =>
              cases demanded : demandNode handle chosen with
              | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [step, requestNode, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      have same := Outcome.yielded.inj (by simpa only [step, requestNode,
                        SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest result value _ after tail.steps
                      obtain ⟨original, stored, retained⟩ := SourceRecursiveIntersectionNative.demandNode_ready
                        handle chosen running result demanded
                      have available := (chosenValid.nodes.checked handle ⟨original, .returned result⟩ stored).2
                      simpa only [retained] using available
                  | evaluate actual =>
                      have same := Outcome.yielded.inj (by simpa only [step, requestNode,
                        SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      obtain ⟨inner, outer, result, middle, _, _, finished⟩ := bind_inverse rest
                        (.code (compileNode actual)) (fun result => .finishNode handle result (.pure result))
                        ⟨running, before.operations⟩ after value tail
                      exact (finish_node_result outer handle result value middle after finished).2

/-- An actual completed request derives result availability without original or closed operand premises. -/
theorem node_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Available after.native.machine.heap value := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none =>
      have same := SourceCurrentNativeRowKeyable.unkeyed_empty request fuel value requested trace
      rw [same]
      exact empty_available _
  | some key => exact keyed_result fuel request before after value valid key requested trace

end MicroCFTA.SourceCurrentNativeOpenRequestResults
