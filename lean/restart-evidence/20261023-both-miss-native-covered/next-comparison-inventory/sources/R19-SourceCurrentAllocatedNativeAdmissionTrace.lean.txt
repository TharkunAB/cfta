import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCode
import MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Source admission certificates along actual checked traces

Every source expansion has a static certificate for its exact request.
Physical trace checks derive each actual returned machine and resident hit.
The simulation retains local admission before every publication instruction.
No recursive result law or future successful execution is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeAdmissionCache SourceCurrentAllocatedNativeAdmissionCode
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "PhysicalInputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat} {A : Type}
variable (source : InternedConstructorTemplates.State Symbol Guard)
  (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))

/-- Static source branch proofs certify code without executing a recursive request. -/
structure Branches [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] : Prop where
  nodes : ∀ request : NodeRequest Symbol Guard, NodeScope source request → NodeCovered inputs request →
    ∀ machine : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid machine → SemanticReady machine.heap →
    NodeReady machine request → Grows source machine.heap → Extends source.nodes.issued machine.heap.nodes.issued →
    Certified source holds inputs (compileNode request) machine (fun after value => Available after.heap value)
  edges : ∀ request : EdgeRequest Symbol Guard, EdgeScope source request → EdgeCovered inputs request →
    ∀ (before after : Checked width) (code : Code Symbol Guard (EdgeValue Symbol Guard)),
    SourceRecursiveIntersectionKernel.Valid before.native.machine → SemanticReady before.native.machine.heap →
    EdgeReady before.native.machine request → body request .pure before = .yielded (.code code) after →
    Certified source holds inputs code after.native.machine (fun final value => EdgeResident final.heap value)

/-- A demanded edge body retains the original request before its actual prefix runs. -/
def ControlCertified [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => Certified source holds inputs code state post
  | .edgeBody request next => EdgeScope source request ∧ EdgeCovered inputs request ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after → SemanticReady after.heap →
        EdgeResident after.heap value → Certified source holds inputs (next value) after post

/-- The local certificate derives admission at the current publication site. -/
theorem current [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (machine : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : ControlCertified source holds inputs control machine post) :
    SourceCurrentAllocatedNativeAdmissionExecution.RequestCovered inputs control := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact certificate.2.1 | trivial

private theorem yielded_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (before after : Checked width)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (physical : PhysicalInputs control before) (fields : Fields control before)
    (one : step control before = .yielded next after) :
    Good after ∧ SemanticReady after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧ Fields next after := by
  have actual := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
  have retained : Good after ∧ Extension before.native.machine after.native.machine ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (.yielded next after) := by
    simpa only [one, Outcome.state] using actual
  have ready := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control before semantic
    (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before physical)
  exact ⟨retained.1, by simpa only [one, Outcome.state] using ready, retained.2.1, retained.2.2.2.2.2⟩

/-- Each actual yielded instruction retains the source certificate at its exact next control. -/
theorem yielded_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (branches : Branches (width := width) source holds inputs)
    (control next : Control A) (before after : Checked width) (post : Machine Symbol Guard → A → Prop)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (physical : PhysicalInputs control before) (fields : Fields control before)
    (certificate : ControlCertified source holds inputs control before.native.machine post)
    (one : step control before = .yielded next after) :
    ControlCertified source holds inputs next after.native.machine post := by
  have effects := yielded_effects control next before after good semantic physical fields one
  cases control with
  | edgeBody request resume =>
      obtain ⟨code, operations, emitted, _, _, _, _⟩ :=
        SourceCurrentAllocatedNativeFieldClosure.body_complete request .pure before good.operations good.fields
          fields.1 (fun _ => trivial)
      have complete : step (.edgeBody request resume) before =
          .yielded (.code (code.bind resume)) {before with operations := operations} := by
        change body request resume before = _
        have append := body_bind request (fun value => Code.pure value) resume before
        simpa only [Code.bind, emitted, appendStep, Control.bind] using append
      rw [complete] at one
      cases one
      have bodyCertificate := branches.edges request certificate.1 certificate.2.1 before
        {before with operations := operations} code good.native.machine semantic fields.1 emitted
      apply certified_bind source holds inputs code resume before.native.machine good.native.machine semantic
        (fun final value => EdgeResident final.heap value) post bodyCertificate
      intro value final finalValid later finalSemantic resident
      exact certificate.2.2 value final finalValid later finalSemantic resident
  | code code =>
      cases code with
      | pure | fail => simp only [step, SourceRecursiveIntersectionNative.step, lift] at one; cases one
      | work job resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact certificate _ _ rfl effects.1.native.machine effects.2.2.1 effects.2.1
      | enter domain left right first second resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact certificate.2.2
      | read name resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact certificate
      | optionalBinder pair value resume =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap with
          | pending key heap =>
              simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
              cases one
          | done result heap =>
              simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
              cases one
              have call : construction (SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap)
                  before.native.machine = .done result {before.native.machine with heap := heap} := by
                simp only [actual, construction]
              exact certificate _ _ call effects.1.native.machine effects.2.2.1 effects.2.1
      | finishNode handle value resume | finishEdge handle value resume =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
          exact certificate
      | node request resume =>
          cases selected : lookupNode width request before.native with
          | mk selection chosen =>
              cases selection with
              | direct original =>
                  obtain ⟨same, retained⟩ := SourceRecursiveIntersectionNative.lookupNode_direct
                    request original before.native chosen selected
                  subst original
                  subst chosen
                  simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] at one
                  cases one
                  have compiled := branches.nodes request certificate.1 certificate.2.1 before.native.machine
                    good.native.machine semantic physical.1 growth history
                  apply certified_bind source holds inputs _ resume before.native.machine good.native.machine semantic
                    (fun final value => Available final.heap value) post compiled
                  intro value final finalValid later finalSemantic available
                  exact certificate.2.2 value final finalValid later finalSemantic available
              | memoized handle =>
                  obtain ⟨key, requested, _, chosenMachine⟩ :=
                    SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
                  have safe := physical.2 key requested
                  cases demanded : demandNode handle chosen with
                  | mk observation reached =>
                      cases observation with
                      | absent | busy =>
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                      | ready value =>
                          have returned := SourceCurrentAllocatedNativePhysicalCache.node_ready request before.native chosen reached
                            handle value good.native physical.1 safe selected demanded
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          exact certificate.2.2 value reached.machine effects.1.native.machine effects.2.2.1
                            effects.2.1 returned.2.2
                      | evaluate original =>
                          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request original before.native chosen reached
                            handle good.native physical.1 safe selected demanded
                          subst original
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                          cases one
                          have demandMachine : reached.machine = chosen.machine := by
                            simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen
                          have sameMachine : reached.machine = before.native.machine := demandMachine.trans chosenMachine
                          have compiled := branches.nodes request certificate.1 certificate.2.1 reached.machine
                            effects.1.native.machine effects.2.1
                            (by simpa only [sameMachine] using physical.1)
                            (grows_trans growth effects.2.2.1.heap) (extends_trans history effects.2.2.1.history)
                          apply certified_bind source holds inputs _ _ reached.machine effects.1.native.machine effects.2.1
                            (fun final value => Available final.heap value) post compiled
                          intro value final finalValid later finalSemantic available
                          exact certificate.2.2 value final finalValid (effects.2.2.1.trans later) finalSemantic available
      | edge request resume =>
          cases selected : lookupEdge width request before.native with
          | mk handle chosen =>
              cases demanded : demandEdge handle chosen with
              | mk observation reached =>
                  cases observation with
                  | absent | busy => simp only [step, selected, demanded] at one; cases one
                  | ready value =>
                      have returned := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before.native chosen reached
                        handle value good.native physical.1 physical.2 selected demanded
                      simp only [step, selected, demanded] at one
                      cases one
                      exact certificate.2.2 value reached.machine effects.1.native.machine effects.2.2.1 effects.2.1 returned.2.2
                  | evaluate original =>
                      have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request original before.native chosen reached
                        handle good.native physical.1 physical.2 selected demanded
                      subst original
                      simp only [step, selected, demanded] at one
                      cases one
                      refine ⟨certificate.1, certificate.2.1, ?_⟩
                      intro value final finalValid later finalSemantic resident
                      exact certificate.2.2 value final finalValid (effects.2.2.1.trans later) finalSemantic resident

/-- Actual physical traces derive admission at each reached publication and in every final cell. -/
theorem Trace.covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (branches : Branches (width := width) source holds inputs)
    {fuel : Nat} {control next : Control A} {before after : Checked width}
    (trace : Trace fuel control before next after) (post : Machine Symbol Guard → A → Prop)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (fields : Fields control before) (covered : Covered inputs before.native)
    (certificate : ControlCertified source holds inputs control before.native.machine post) :
    Covered inputs after.native ∧ ControlCertified source holds inputs next after.native.machine post := by
  induction trace with
  | refl => exact ⟨covered, certificate⟩
  | cons control before resume reached final result fuel physical one tail ih =>
      have effects := yielded_effects control resume before reached good semantic physical fields one
      have admitted := SourceCurrentAllocatedNativeAdmissionExecution.step_covered inputs control before covered
        (current source holds inputs control before.native.machine post certificate)
      have reachedCovered : Covered inputs reached.native := by simpa only [one, Outcome.state] using admitted
      have nextCertificate := yielded_certified source holds inputs branches control resume before reached post good semantic
        growth history physical fields certificate one
      exact ih effects.1 effects.2.1 (grows_trans growth effects.2.2.1.heap)
        (extends_trans history effects.2.2.1.history) effects.2.2.2 reachedCovered nextCertificate
end MicroCFTA.SourceCurrentAllocatedNativeAdmissionTrace
