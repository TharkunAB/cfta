import MicroCFTA.SourceCurrentAllocatedNativeStoredTrace
import MicroCFTA.SourceCurrentNativeTracePrefixBind

/-!
# Conditional native cache certificates at actual checked prefixes

The proof consumes a finite actual prefix. It does not require a future return.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredPrefix
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityNativeDemandBodyCode
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryStored SourceCurrentAllocatedFiniteOrdinaryCode
open SourceCurrentAllocatedFiniteOrdinaryExecution (CertifiedControl)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

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

/-- Every actual finite prefix from clean source code retains conditional native certificates. -/
theorem clean_prefix_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) {Output : Type} (control : Control Output) (before after : Checked width) (remaining : Control Output)
    (trace : Trace fuel control before remaining after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (fields : Fields control before) (stored : Stored before.native) (clean : Clean control) :
    Stored after.native := by
  classical
  induction fuel using Nat.strongRecOn generalizing Output control before after remaining with
  | ind fuel ih =>
      cases trace with
      | refl => exact stored
      | cons start initial rest current final after count inputs one tail =>
          have entryTrace : Trace 1 control before rest current :=
            .cons _ _ _ _ _ _ 0 inputs one (.refl _ _)
          have advanced := reached entryTrace good semantic fields
          cases control with
          | edgeBody request next =>
              have restClean := SourceEqualityNativeDemandBodyCode.body_clean request next before current rest one clean
              have nativeSame : current.native = before.native := by
                have same := SourceEqualityNativeDemandOperations.body_native request next before
                simpa only [show body request next before = .yielded rest current from one, Outcome.state] using same
              exact ih count (by omega) rest current after remaining tail advanced.1 advanced.2.2.1
                advanced.2.2.2 (nativeSame ▸ stored) restClean
          | code code =>
              cases code with
              | pure | fail => cases one
              | finishNode | finishEdge => cases clean
              | work job next | enter domain left right first second next | read name next =>
                  have same := Outcome.yielded.inj one
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  exact ih count (by omega) _ _ after remaining tail advanced.1 advanced.2.2.1
                    advanced.2.2.2 ⟨stored.nodes, stored.edges⟩ (clean _)
              | optionalBinder pair pending next =>
                  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair pending before.native.machine.heap with
                  | pending =>
                      simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                      cases one
                  | done result heap =>
                      simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                      have same := Outcome.yielded.inj one
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      exact ih count (by omega) _ _ after remaining tail advanced.1 advanced.2.2.1
                        advanced.2.2.2 ⟨stored.nodes, stored.edges⟩ (clean _)
              | node request next =>
                  cases selected : lookupNode width request before.native with
                  | mk selection chosen =>
                      cases selection with
                      | direct actual =>
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] at one
                          have same := Outcome.yielded.inj one
                          rcases same.1 with rfl
                          rcases same.2 with rfl
                          have chosenStored : Stored chosen := by
                            simpa only [selected] using lookupNode_stored before.native request stored
                          exact ih count (by omega) _ _ after remaining tail advanced.1 advanced.2.2.1
                            advanced.2.2.2 chosenStored (bodyCode_bind _ _ (compileNode_bodyCode actual) clean)
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
                                  exact ih count (by omega) _ _ after remaining tail advanced.1 advanced.2.2.1
                                    advanced.2.2.2 observed.2.1 (clean result)
                              | evaluate actual =>
                                  have started := node_started request actual before.native chosen running handle
                                    good.native stored inputs.1 safe selected demanded
                                  obtain ⟨ownerSame, runningStored, runningCell⟩ := started
                                  subst actual
                                  have same := Outcome.yielded.inj (by simpa only [step, SourceRecursiveIntersectionNative.step,
                                    selected, demanded, lift] using one)
                                  rcases same.1 with rfl
                                  rcases same.2 with rfl
                                  have bodyFields := SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
                                    (.code (compileNode request)) (fun result => .finishNode handle result (next result)) _ advanced.2.2.2
                                  rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases count (.code (compileNode request))
                                      (fun result => .finishNode handle result (next result))
                                      ⟨running, before.operations⟩ after remaining tail with
                                      ⟨inner, bodyPrefix, _nonpure, _same⟩ |
                                      ⟨inner, outer, result, middle, total, bodyTrace, frameTrace⟩
                                  · exact ih count (by omega) _ _ after inner bodyPrefix advanced.1 advanced.2.2.1
                                      bodyFields runningStored (compileNode_bodyCode request)
                                  ·
                                    have machineSame : running.machine = before.native.machine := by
                                      have first := SourceRecursiveIntersectionNative.lookupNode_machine request before.native
                                      have second := SourceRecursiveIntersectionNative.demandNode_machine handle chosen
                                      simp only [selected] at first
                                      simp only [demanded] at second
                                      exact second.trans first
                                    have built : Stored middle.native ∧ NodeCertificate request result := by
                                      by_cases ordinary : NodeInputs request
                                      · have bodyCert := SourceCurrentAllocatedFiniteOrdinaryNode.node_certified request running.machine
                                          advanced.1.native.machine advanced.2.2.1
                                          (by rw [machineSame]; exact inputs.1.2.1) (by rw [machineSame]; exact inputs.1.2.2) ordinary
                                        exact SourceCurrentAllocatedFiniteOrdinaryExecution.verified inner _ _ middle result
                                          (fun _ result => NodeCertificate request result) bodyTrace advanced.1 advanced.2.2.1
                                          bodyFields runningStored bodyCert
                                      · refine ⟨SourceCurrentAllocatedNativeStoredTrace.clean_trace_stored inner _ _ middle result bodyTrace advanced.1 advanced.2.2.1
                                          bodyFields runningStored (compileNode_bodyCode request), ?_⟩
                                        intro seen leftDomain rightDomain
                                        exact (ordinary ⟨seen, leftDomain, rightDomain⟩).elim
                                    have bodyReached := reached bodyTrace advanced.1 advanced.2.2.1 bodyFields
                                    let finished : Checked width := {middle with native := finishNode handle result middle.native}
                                    cases frameTrace with
                                    | refl => exact built.1
                                    | cons frame initial rest current final after countFinish frameInputs oneFinish restTrace =>
                                        have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.node_body_cell
                                          inner handle request _ middle result bodyTrace advanced.1.native runningCell
                                        have finishSame := Outcome.yielded.inj
                                          (show Outcome.yielded (.code (next result)) finished = Outcome.yielded rest current from oneFinish)
                                        rcases finishSame.1 with rfl
                                        rcases finishSame.2 with rfl
                                        have frameFields := (reached (bodyTrace.bind (fun result => .finishNode handle result (next result)))
                                          advanced.1 advanced.2.2.1 advanced.2.2.2).2.2.2
                                        have finishPrefix : Trace 1 (.code (.finishNode handle result (next result))) middle
                                            (.code (next result)) finished := .cons _ _ _ _ _ _ 0 frameInputs rfl (.refl _ _)
                                        have finishedReached := reached finishPrefix bodyReached.1 bodyReached.2.2.1 frameFields
                                        exact ih countFinish (by omega) _ finished after remaining restTrace finishedReached.1
                                          finishedReached.2.2.1 finishedReached.2.2.2
                                          (finishNode_stored middle.native handle request result built.1 retained.1 built.2) (clean result)
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
                              exact ih count (by omega) _ _ after remaining tail advanced.1 advanced.2.2.1
                                advanced.2.2.2 observed.2.1 (clean result)
                          | evaluate actual =>
                              have started := edge_started request actual before.native chosen running handle
                                good.native stored inputs.1 inputs.2 selected demanded
                              obtain ⟨ownerSame, runningStored, runningCell⟩ := started
                              subst actual
                              have same := Outcome.yielded.inj (by simpa only [step, selected, demanded] using one)
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              have bodyFields := SourceCurrentAllocatedNativeSemanticTraceReadback.fields_before_bind
                                (.edgeBody request .pure) (fun result => .finishEdge handle result (next result)) _ advanced.2.2.2
                              rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases count (.edgeBody request .pure)
                                  (fun result => .finishEdge handle result (next result))
                                  ⟨running, before.operations⟩ after remaining tail with
                                  ⟨inner, bodyPrefix, _nonpure, _same⟩ |
                                  ⟨inner, outer, result, middle, total, bodyTrace, frameTrace⟩
                              · exact ih count (by omega) _ _ after inner bodyPrefix advanced.1 advanced.2.2.1
                                  bodyFields runningStored (fun _ => trivial)
                              ·
                                have built : Stored middle.native ∧ EdgeCertificate request result := by
                                  by_cases ordinary : EdgeInputs request
                                  · have bodyCert : CertifiedControl (.edgeBody request .pure) running.machine
                                        (fun _ result => EdgeCertificate request result) := ⟨ordinary, fun _ _ _ _ _ _ law => law⟩
                                    exact SourceCurrentAllocatedFiniteOrdinaryExecution.verified inner _ _ middle result
                                      (fun _ result => EdgeCertificate request result) bodyTrace advanced.1 advanced.2.2.1
                                      bodyFields runningStored bodyCert
                                  · refine ⟨SourceCurrentAllocatedNativeStoredTrace.clean_trace_stored inner _ _ middle result bodyTrace advanced.1 advanced.2.2.1
                                      bodyFields runningStored (fun _ => trivial), ?_⟩
                                    intro seen leftDomain rightDomain
                                    exact (ordinary ⟨seen, leftDomain, rightDomain⟩).elim
                                have bodyReached := reached bodyTrace advanced.1 advanced.2.2.1 bodyFields
                                let finished : Checked width := {middle with native := finishEdge handle result middle.native}
                                cases frameTrace with
                                | refl => exact built.1
                                | cons frame initial rest current final after countFinish frameInputs oneFinish restTrace =>
                                    have retained := SourceCurrentAllocatedFiniteOrdinaryFrames.edge_body_cell
                                      inner handle request _ middle result bodyTrace advanced.1.native runningCell
                                    have finishSame := Outcome.yielded.inj
                                      (show Outcome.yielded (.code (next result)) finished = Outcome.yielded rest current from oneFinish)
                                    rcases finishSame.1 with rfl
                                    rcases finishSame.2 with rfl
                                    have frameFields := (reached (bodyTrace.bind (fun result => .finishEdge handle result (next result)))
                                      advanced.1 advanced.2.2.1 advanced.2.2.2).2.2.2
                                    have finishPrefix : Trace 1 (.code (.finishEdge handle result (next result))) middle
                                        (.code (next result)) finished := .cons _ _ _ _ _ _ 0 frameInputs rfl (.refl _ _)
                                    have finishedReached := reached finishPrefix bodyReached.1 bodyReached.2.2.1 frameFields
                                    exact ih countFinish (by omega) _ finished after remaining restTrace finishedReached.1
                                      finishedReached.2.2.1 finishedReached.2.2.2
                                      (finishEdge_stored middle.native handle request result built.1 retained.1 built.2) (clean result)

private theorem terminal_step_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {Output : Type} (control : Control Output) (before : Checked width) (stored : Stored before.native) :
    match step control before with
    | .yielded .. => True
    | observed => Stored observed.state.native := by
  cases control with
  | edgeBody request next =>
      have same := SourceEqualityNativeDemandOperations.body_native request next before
      cases actual : body request next before <;>
        simp only [step, actual, Outcome.state] at same ⊢
      all_goals first | trivial | (rw [same]; exact stored)
  | code code =>
      cases code with
      | pure | fail => exact stored
      | work | enter | read | finishNode | finishEdge => trivial
      | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value before.native.machine.heap <;>
            simp only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state]
          all_goals first | trivial | exact ⟨stored.nodes, stored.edges⟩
      | node request next =>
          cases selected : lookupNode width request before.native with
          | mk selection chosen =>
              have chosenStored : Stored chosen := by
                simpa only [selected] using lookupNode_stored before.native request stored
              cases selection with
              | direct actual =>
                  simp only [step, SourceRecursiveIntersectionNative.step, selected, lift]
              | memoized handle =>
                  cases demanded : demandNode handle chosen with
                  | mk observation running =>
                      have runningStored : Stored running := by
                        simpa only [demanded] using demandNode_stored chosen handle chosenStored
                      cases observation <;>
                        simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift, Outcome.state]
                      all_goals trivial
      | edge request next =>
          cases selected : lookupEdge width request before.native with
          | mk handle chosen =>
              have chosenStored : Stored chosen := by
                simpa only [selected] using lookupEdge_stored before.native request stored
              cases demanded : demandEdge handle chosen with
              | mk observation running =>
                  have runningStored : Stored running := by
                    simpa only [demanded] using demandEdge_stored chosen handle chosenStored
                  cases observation <;>
                    simp only [step, selected, demanded, Outcome.state]
                  all_goals trivial

/-- The actual terminal step after a checked prefix retains native certificates in its returned state. -/
theorem terminal_prefix_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) {Output : Type} (control remaining : Control Output) (before after : Checked width)
    (trace : Trace fuel control before remaining after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (fields : Fields control before) (stored : Stored before.native) (clean : Clean control) :
    match step remaining after with
    | .yielded .. => True
    | observed => Stored observed.state.native :=
  terminal_step_stored remaining after (clean_prefix_stored fuel control before after remaining trace good semantic fields stored clean)

/-- A literal node request retains native certificates at every observed finite prefix. -/
theorem node_prefix_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width) (fuel : Nat)
    (remaining : Control (Value Symbol Guard))
    (trace : Trace fuel (.code (requestNode request.domain request.left request.right)) before remaining after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (stored : Stored before.native) :
    Stored after.native :=
  clean_prefix_stored fuel _ before after remaining trace good semantic (fun _ => trivial) stored (fun _ => trivial)

/-- A literal edge request retains native certificates at every observed finite prefix. -/
theorem edge_prefix_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (before after : Checked width) (fuel : Nat)
    (remaining : Control (EdgeValue Symbol Guard))
    (trace : Trace fuel (.code (requestEdge request.domain request.left request.right)) before remaining after)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap) (stored : Stored before.native) :
    Stored after.native :=
  clean_prefix_stored fuel _ before after remaining trace good semantic (fun _ => trivial) stored (fun _ => trivial)

/-- The existing literal initializer derives its native invariant before every observed prefix. -/
theorem initial_clean_prefix_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (fuel : Nat) {Output : Type} (control remaining : Control Output) (after : Checked width)
    (trace : Trace fuel control (SourceCurrentAllocatedPartialInitialization.checked width cache heap) remaining after)
    (good : Good (SourceCurrentAllocatedPartialInitialization.checked width cache heap))
    (semantic : SemanticReady heap)
    (fields : Fields control (SourceCurrentAllocatedPartialInitialization.checked width cache heap))
    (clean : Clean control) : Stored after.native :=
  clean_prefix_stored fuel control _ after remaining trace good semantic fields
    (initial_stored width ⟨heap, Cache.emptyState⟩) clean

end MicroCFTA.SourceCurrentAllocatedNativeStoredPrefix
