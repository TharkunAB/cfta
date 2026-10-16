import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceEqualityNativeDemandNodeReadback

/-!
# Physical results of actual completed requests

Actual warm hits read resident returned cells. Actual cold calls cross their
checked finish frame. Result availability follows from those observations.
No child language law or result postcondition supplies the conclusion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRequestResults
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeSemanticTraceReadback (bind_inverse)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- A completed node finish checks its literal returned value before publication. -/
theorem finish_node_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (result value : Value Symbol Guard) (before after : Checked width)
    (trace : Trace fuel (.code (.finishNode handle result (.pure result))) before (.code (.pure value)) after) :
    result = value ∧ Available after.native.machine.heap value := by
  cases trace with
  | cons _ _ next current _ _ rest inputs one tail =>
      have same := Outcome.yielded.inj one
      rcases same.1 with rfl
      rcases same.2 with rfl
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest result value _ after tail.steps
      exact ⟨rfl, inputs.choose_spec.2⟩

/-- A completed edge finish checks its literal returned row before publication. -/
theorem finish_edge_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (result value : EdgeValue Symbol Guard) (before after : Checked width)
    (trace : Trace fuel (.code (.finishEdge handle result (.pure result))) before (.code (.pure value)) after) :
    result = value ∧ EdgeResident after.native.machine.heap value := by
  cases trace with
  | cons _ _ next current _ _ rest inputs one tail =>
      have same := Outcome.yielded.inj one
      rcases same.1 with rfl
      rcases same.2 with rfl
      obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest result value _ after tail.steps
      exact ⟨rfl, inputs.choose_spec.2⟩

/-- Original operands always select a physical memo key, independently of key bounds. -/
theorem original_key (request : NodeRequest Symbol Guard)
    (left : Original request.left) (right : Original request.right) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key :=
  ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _ _ _
    (left.codec request.left) (right.codec request.right)⟩

/-- A completed original node request derives availability from its actual hit or finish. -/
theorem node_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : NodeRequest Symbol Guard) (before after : Checked width) (value : Value Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (left : Original request.left) (right : Original request.right)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after) :
    Available after.native.machine.heap value := by
  obtain ⟨key, requested⟩ := original_key request left right
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

/-- A completed edge request derives residency from its actual hit or finish. -/
theorem edge_result [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (before after : Checked width) (value : EdgeValue Symbol Guard)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after) :
    EdgeResident after.native.machine.heap value := by
  cases trace with
  | cons _ _ next current _ _ rest inputs one tail =>
      have chosenValid := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid before.native valid request inputs.1 inputs.2
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
          simp only [selected] at chosenValid
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
              cases observation with
              | absent | busy => simp only [step, requestEdge, selected, demanded] at one; cases one
              | ready result =>
                  have same := Outcome.yielded.inj (by simpa only [step, requestEdge, selected, demanded] using one)
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  obtain ⟨rfl, rfl, rfl⟩ := pure_trace rest result value _ after tail.steps
                  obtain ⟨original, stored, retained⟩ := SourceRecursiveIntersectionNative.demandEdge_ready
                    handle chosen running result demanded
                  have resident := (chosenValid.edges.checked handle ⟨original, .returned result⟩ stored).2
                  simpa only [retained] using resident
              | evaluate actual =>
                  have same := Outcome.yielded.inj (by simpa only [step, requestEdge, selected, demanded] using one)
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  obtain ⟨inner, outer, result, middle, _, _, finished⟩ := bind_inverse rest
                    (.edgeBody actual .pure) (fun result => .finishEdge handle result (.pure result))
                    ⟨running, before.operations⟩ after value tail
                  exact (finish_edge_result outer handle result value middle after finished).2

end MicroCFTA.SourceCurrentAllocatedNativeRequestResults
