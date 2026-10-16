import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFrames
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback

/-!
# Structural verification of actual finite ordinary native requests

The proof follows the literal checked trace. Recursive bodies have shorter
traces. Each body derives its result certificate before its original finish
frame installs that result. Warm hits use their exact captured requests.
No future body law or historical eager execution supplies the result.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryExecution
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored
open SourceCurrentAllocatedFiniteOrdinaryCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- Checked edge bodies have the same local structural continuation law as edge requests. -/
def CertifiedControl [DecidableEq (EdgeKey Symbol Guard)] (control : Control A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => Certified code state post
  | .edgeBody request next => EdgeInputs request ∧ ∀ value after,
      SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
      EdgeResident after.heap value → EdgeCertificate request value → Certified (next value) after post

private theorem trace_semantic [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (semantic : SemanticReady before.native.machine.heap) :
    SemanticReady after.native.machine.heap := by
  induction trace with
  | refl => exact semantic
  | cons control before next middle final after count inputs one tail ih =>
      have current := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control before semantic
        (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)
      rw [one] at current
      exact ih current

private theorem reached [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (trace : Trace fuel control before rest after) (good : Good before)
    (semantic : SemanticReady before.native.machine.heap) (fields : Fields control before) :
    Good after ∧ Extension before.native.machine after.native.machine ∧
      SemanticReady after.native.machine.heap ∧ Fields rest after := by
  have physical := SourceCurrentAllocatedNativeSemanticTraceReadback.effects trace good fields
  exact ⟨physical.1, physical.2.1, trace_semantic trace semantic, physical.2.2.2.2⟩

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

private theorem node_cacheable (request : NodeRequest Symbol Guard) (inputs : NodeInputs request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases request with ⟨domain, left, right⟩
  rcases inputs with ⟨_, leftDomain, rightDomain⟩
  cases leftDomain <;> cases rightDomain <;> exact ⟨_, rfl⟩


end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryExecution
