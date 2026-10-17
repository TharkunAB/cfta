import MicroCFTA.SourceCurrentNativeGuardCode
import MicroCFTA.SourceCurrentNativeGuardAlphabet
import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Finite guard alphabets through actual native instructions

One alphabet extension covers each checked instruction. Actual row
residency supplies each conjunction operand. Captured code retains its
literal guard checks at the larger alphabet.
-/
namespace MicroCFTA.SourceCurrentNativeGuardStep
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentNativeGuardAlphabet (step mem_step_of_mem top_mem_step conjoin_mem_step)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "CodeFields" => SourceCurrentNativeGuardCode.Fields
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {A : Type} {width : Nat}

/-- Both checked control forms retain the static checks in their captured code. -/
def Fields (alphabet : List Guard) : Control A → Prop
  | .code code => CodeFields (fun guard => guard ∈ alphabet) code
  | .edgeBody _ next => ∀ value, CodeFields (fun guard => guard ∈ alphabet) (next value)

/-- Alphabet inclusion retains every physical edge record check. -/
theorem heap_mono {first last : List Guard} (increase : first ⊆ last)
    {heap : InternedConstructorTemplates.State Symbol Guard}
    (known : Heap (fun guard => guard ∈ first) heap) : Heap (fun guard => guard ∈ last) heap :=
  fun key edge present => increase (known key edge present)

/-- Alphabet inclusion retains all static captured checks. -/
theorem fields_mono {first last : List Guard} (increase : first ⊆ last)
    (control : Control A) (fields : Fields first control) : Fields last control := by
  cases control with
  | code code => exact SourceCurrentNativeGuardCode.mono _ _ (fun _ member => increase member) code fields
  | edgeBody request next =>
      exact fun value => SourceCurrentNativeGuardCode.mono _ _ (fun _ member => increase member) (next value) (fields value)

private theorem lift_native (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native = outcome.state := by cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual checked step retains its physical carrier before the common extension. -/
theorem step_heap (alphabet : List Guard) (control : Control A) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (fields : Fields alphabet control) :
    Heap (fun guard => guard ∈ alphabet) (SourceEqualityNativeDemand.step control before).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [SourceEqualityNativeDemand.step, SourceEqualityNativeDemandOperations.body_native]
      exact known
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact known
      | work job next => exact SourceEqualityAnnotationHeap.run _ job fields.1 before.native.machine.heap known
      | optionalBinder pair body next =>
          have retained := SourceEqualityAnnotationStoredSyntax.optionalBinder _ pair body before.native.machine.heap
            known good.native.machine.1 inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual,
                lift, Outcome.state, SourceRecursiveIntersectionThunks.advance, InternedNestedConstruction.Outcome.state] using retained
      | node request next =>
          change Heap _ (lift before.operations (SourceRecursiveIntersectionNative.step
            SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap
          rw [lift_native, SourceRecursiveIntersectionNative.node_step_machine]
          exact known
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact known

/-- An actual yielded control derives its next static checks at one alphabet extension. -/
theorem yielded_fields (alphabet : List Guard) (control rest : Control A) (before after : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (allocated : SourceCurrentAllocatedNativeFieldClosure.Fields control before)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (fields : Fields alphabet control)
    (one : SourceEqualityNativeDemand.step control before = .yielded rest after) :
    Fields (step alphabet) rest := by
  have widened := fields_mono (fun _ member => mem_step_of_mem member) control fields
  cases control with
  | edgeBody request next =>
      have ready := allocated.1
      have cached : SourceEqualityNativeDemandOperations.Fields (.edgeBody request next) :=
        ⟨(good.fields _ _ ready.2.1).1, (good.fields _ _ ready.2.2).1⟩
      obtain ⟨code, rfl, retained⟩ := SourceCurrentNativeGuardCode.body_fields
        (fun guard => guard ∈ step alphabet) request next before after rest good.operations cached
        (top_mem_step alphabet) (conjoin_mem_step (known _ _ ready.2.1) (known _ _ ready.2.2)) widened one
      exact retained
  | code code =>
      cases code with
      | pure | fail => cases one
      | work job next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact widened.2 _
      | enter domain left right first second next | read name next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact widened _
      | optionalBinder pair body next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
          | pending key heap =>
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
              cases one
          | done value heap =>
              simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual, lift] at one
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
              exact widened value
      | node request next =>
          obtain ⟨_machine, _operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.node_yielded
            request next before rest after good.native inputs.1 inputs.2 one
          rcases branches with ⟨rfl, _same⟩ | ⟨value, rfl, _available⟩ | ⟨handle, rfl, _running⟩
          · exact SourceCurrentNativeGuardCode.bind _ _ _ (SourceCurrentNativeGuardCode.compileNode_fields _ request) widened
          · exact widened value
          · exact SourceCurrentNativeGuardCode.bind _ _ _ (SourceCurrentNativeGuardCode.compileNode_fields _ request) widened
      | edge request next =>
          obtain ⟨_machine, _operations, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.edge_yielded
            request next before rest after good.native inputs.1 inputs.2 one
          rcases branches with ⟨value, rfl, _resident⟩ | ⟨handle, rfl, _running⟩
          · exact widened value
          · exact widened
      | finishNode handle value next | finishEdge handle value next =>
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact widened

end MicroCFTA.SourceCurrentNativeGuardStep
