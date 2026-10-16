import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdge
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

/-- A completed certified source trace derives its own structural result and retained warm certificates. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) {Output : Type} (control : Control Output) (before after : Checked width) (value : Output)
    (post : Machine Symbol Guard → Output → Prop)
    (trace : Trace fuel control before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (fields : Fields control before) (stored : Stored before.native)
    (certificate : CertifiedControl control before.native.machine post) :
    Stored after.native ∧ post after.native.machine value := by
  induction fuel using Nat.strongRecOn generalizing Output control before after value with
  | ind fuel ih =>
      cases trace with
      | refl => exact ⟨stored, certificate⟩
      | cons start initial rest current final after count inputs one tail =>
          have entryTrace : Trace 1 control before rest current :=
            .cons _ _ _ _ _ _ 0 inputs one (.refl _ _)
          have advanced := reached entryTrace good semantic fields
          cases control with
          | edgeBody request next =>
              obtain ⟨restCode, restSame⟩ := SourceCurrentAllocatedFiniteOrdinaryEdge.body_yielded_code
                request next before current rest one
              subst rest
              have continuationCert := SourceCurrentAllocatedFiniteOrdinaryEdge.body_certified
                request certificate.1 before current next restCode good semantic one post certificate.2
              have nativeSame : current.native = before.native := by
                have same := SourceEqualityNativeDemandOperations.body_native request next before
                simpa only [show body request next before = .yielded (.code restCode) current from one, Outcome.state] using same
              exact ih count (by omega) (.code restCode) current after value post tail advanced.1 advanced.2.2.1
                advanced.2.2.2 (nativeSame ▸ stored) continuationCert
          | code code =>
              cases code with
              | pure | fail => cases one
              | enter | read | optionalBinder | finishNode | finishEdge => cases certificate
              | work job next =>
                  have same := Outcome.yielded.inj one
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  have continuationCert := certificate (run job before.native.machine.heap).1
                    {before.native.machine with heap := (run job before.native.machine.heap).2}
                    rfl inputs advanced.1.native.machine advanced.2.1 advanced.2.2.1
                  exact ih count (by omega) _ _ after value post tail advanced.1 advanced.2.2.1
                    advanced.2.2.2 (advance_stored _ _ stored) continuationCert
              | node request next =>
                  cases selected : lookupNode width request before.native with
                  | mk selection chosen =>
                      cases selection with
                      | direct actual =>
                          obtain ⟨key, known⟩ := node_cacheable (width := width) request certificate.1
                          simp only [lookupNode, known] at selected
                          cases selected
                      | memoized handle =>
                          have safe := selected_node_safe request before.native chosen handle inputs.2 selected
                          cases demanded : demandNode handle chosen with
                          | mk observation running =>
                              cases observation with
                              | absent | busy =>
                                  simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                                  cases one
                              | ready result =>
                                  have observed := node_observed_ready request before.native chosen running handle result
                                    good.native stored inputs.1 safe selected demanded
                                  have same := Outcome.yielded.inj (by simpa only [step, SourceRecursiveIntersectionNative.step,
                                    selected, demanded, lift] using one)
                                  rcases same.1 with rfl
                                  rcases same.2 with rfl
                                  exact ih count (by omega) _ _ after value post tail advanced.1 advanced.2.2.1
                                    advanced.2.2.2 observed.2.1
                                    (certificate.2 result _ advanced.1.native.machine advanced.2.1 advanced.2.2.1 observed.2.2.2 observed.1)
                              | evaluate actual =>
                                  have started := node_started request actual before.native chosen running handle
                                    good.native stored inputs.1 safe selected demanded
                                  obtain ⟨ownerSame, runningStored, runningCell⟩ := started
                                  subst actual
                                  have same := Outcome.yielded.inj (by simpa only [step, SourceRecursiveIntersectionNative.step,
                                    selected, demanded, lift] using one)
                                  rcases same.1 with rfl
                                  rcases same.2 with rfl
                                  obtain ⟨inner, outer, result, middle, total, bodyTrace, frameTrace⟩ :=
                                    SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse count (.code (compileNode request))
                                      (fun result => .finishNode handle result (next result))
                                      ⟨running, before.operations⟩ after value tail
                                  have bodyFields := SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
                                    (.code (compileNode request)) (fun result => .finishNode handle result (next result)) _ advanced.2.2.2
                                  have machineSame : running.machine = before.native.machine := by
                                    have first := SourceRecursiveIntersectionNative.lookupNode_machine request before.native
                                    have second := SourceRecursiveIntersectionNative.demandNode_machine handle chosen
                                    simp only [selected] at first
                                    simp only [demanded] at second
                                    exact second.trans first
                                  have bodyCert := SourceCurrentAllocatedFiniteOrdinaryNode.node_certified request running.machine
                                    advanced.1.native.machine advanced.2.2.1
                                    (by rw [machineSame]; exact inputs.1.2.1) (by rw [machineSame]; exact inputs.1.2.2) certificate.1
                                  have built := ih inner (by omega) _ _ middle result (fun _ result => NodeCertificate request result)
                                    bodyTrace advanced.1 advanced.2.2.1 bodyFields runningStored bodyCert
                                  have bodyReached := reached bodyTrace advanced.1 advanced.2.2.1 bodyFields
                                  have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.node_body_cell
                                    inner handle request _ middle result bodyTrace advanced.1.native runningCell
                                  have frameInputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs frameTrace
                                  have available : Available middle.native.machine.heap result := frameInputs.choose_spec.2
                                  let finished : Checked width := {middle with native := finishNode handle result middle.native}
                                  have finishStep : step (.code (.finishNode handle result (next result))) middle =
                                      .yielded (.code (next result)) finished := rfl
                                  obtain ⟨remaining, frameCount, restTrace⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.after_step
                                    outer _ _ middle finished after value frameTrace finishStep
                                  have frameFields := (reached (bodyTrace.bind (fun result => .finishNode handle result (next result)))
                                    advanced.1 advanced.2.2.1 advanced.2.2.2).2.2.2
                                  have finishPrefix : Trace 1 (.code (.finishNode handle result (next result))) middle
                                      (.code (next result)) finished := .cons _ _ _ _ _ _ 0 frameInputs finishStep (.refl _ _)
                                  have finishedReached := reached finishPrefix bodyReached.1 bodyReached.2.2.1 frameFields
                                  have continuationCert := certificate.2 result finished.native.machine finishedReached.1.native.machine
                                    (advanced.2.1.trans (bodyReached.2.1.trans finishedReached.2.1)) finishedReached.2.2.1 available built.2
                                  exact ih remaining (by omega) _ finished after value post restTrace finishedReached.1
                                    finishedReached.2.2.1 finishedReached.2.2.2
                                    (finishNode_stored middle.native handle request result built.1 retained.1 built.2) continuationCert
              | edge request next =>
                  cases selected : lookupEdge width request before.native with
                  | mk handle chosen =>
                      cases demanded : demandEdge handle chosen with
                      | mk observation running =>
                          cases observation with
                          | absent | busy => simp only [step, selected, demanded] at one; cases one
                          | ready result =>
                              have observed := edge_observed_ready request before.native chosen running handle result
                                good.native stored inputs.1 inputs.2 selected demanded
                              have same := Outcome.yielded.inj (by simpa only [step, selected, demanded] using one)
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              exact ih count (by omega) _ _ after value post tail advanced.1 advanced.2.2.1
                                advanced.2.2.2 observed.2.1
                                (certificate.2 result _ advanced.1.native.machine advanced.2.1 advanced.2.2.1 observed.2.2.2 observed.1)
                          | evaluate actual =>
                              have started := edge_started request actual before.native chosen running handle
                                good.native stored inputs.1 inputs.2 selected demanded
                              obtain ⟨ownerSame, runningStored, runningCell⟩ := started
                              subst actual
                              have same := Outcome.yielded.inj (by simpa only [step, selected, demanded] using one)
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              obtain ⟨inner, outer, result, middle, total, bodyTrace, frameTrace⟩ :=
                                SourceCurrentAllocatedNativeSemanticTraceReadback.bind_inverse count (.edgeBody request .pure)
                                  (fun result => .finishEdge handle result (next result))
                                  ⟨running, before.operations⟩ after value tail
                              have bodyFields := SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
                                (.edgeBody request .pure) (fun result => .finishEdge handle result (next result)) _ advanced.2.2.2
                              have bodyCert : CertifiedControl (.edgeBody request .pure) running.machine
                                  (fun _ result => EdgeCertificate request result) := ⟨certificate.1, fun _ _ _ _ _ _ law => law⟩
                              have built := ih inner (by omega) _ _ middle result (fun _ result => EdgeCertificate request result)
                                bodyTrace advanced.1 advanced.2.2.1 bodyFields runningStored bodyCert
                              have bodyReached := reached bodyTrace advanced.1 advanced.2.2.1 bodyFields
                              have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.edge_body_cell
                                inner handle request _ middle result bodyTrace advanced.1.native runningCell
                              have frameInputs := SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs frameTrace
                              have resident : EdgeResident middle.native.machine.heap result := frameInputs.choose_spec.2
                              let finished : Checked width := {middle with native := finishEdge handle result middle.native}
                              have finishStep : step (.code (.finishEdge handle result (next result))) middle =
                                  .yielded (.code (next result)) finished := rfl
                              obtain ⟨remaining, frameCount, restTrace⟩ := SourceCurrentAllocatedNativeSemanticTraceReadback.after_step
                                outer _ _ middle finished after value frameTrace finishStep
                              have frameFields := (reached (bodyTrace.bind (fun result => .finishEdge handle result (next result)))
                                advanced.1 advanced.2.2.1 advanced.2.2.2).2.2.2
                              have finishPrefix : Trace 1 (.code (.finishEdge handle result (next result))) middle
                                  (.code (next result)) finished := .cons _ _ _ _ _ _ 0 frameInputs finishStep (.refl _ _)
                              have finishedReached := reached finishPrefix bodyReached.1 bodyReached.2.2.1 frameFields
                              have continuationCert := certificate.2 result finished.native.machine finishedReached.1.native.machine
                                (advanced.2.1.trans (bodyReached.2.1.trans finishedReached.2.1)) finishedReached.2.2.1 resident built.2
                              exact ih remaining (by omega) _ finished after value post restTrace finishedReached.1
                                finishedReached.2.2.1 finishedReached.2.2.2
                                (finishEdge_stored middle.native handle request result built.1 retained.1 built.2) continuationCert

/-- A completed literal node request derives domain closure, both height bounds, and stored certificates. -/
theorem node_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width) (fuel : Nat) (value : Value Symbol Guard)
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (stored : Stored before.native) (inputs : NodeInputs request) :
    Stored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height request.left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height request.right := by
  have checked := verified fuel _ before after value (fun _ value => NodeCertificate request value)
    trace good semantic (fun _ => trivial) stored (request_node request _ inputs)
  exact ⟨checked.1, checked.2 inputs.1 inputs.2.1 inputs.2.2⟩

/-- A completed literal checked edge request derives both original-forest height bounds. -/
theorem edge_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (fuel : Nat) (value : EdgeValue Symbol Guard)
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before (.code (.pure value)) after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (stored : Stored before.native) (inputs : EdgeInputs request) :
    Stored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Edge value ∧
      MergedOrdinaryHeight.edgeHeight value ≤ MergedOrdinaryHeight.edgeHeight request.left ∧
      MergedOrdinaryHeight.edgeHeight value ≤ MergedOrdinaryHeight.edgeHeight request.right := by
  have checked := verified fuel _ before after value (fun _ value => EdgeCertificate request value)
    trace good semantic (fun _ => trivial) stored (request_edge request _ inputs)
  exact ⟨checked.1, checked.2 inputs.1 inputs.2.1 inputs.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryExecution
