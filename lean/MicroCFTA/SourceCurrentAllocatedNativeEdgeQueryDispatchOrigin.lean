import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
import MicroCFTA.SourceEqualityNativeDemandMemo
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentNativeEnterCommonOperand
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit
import MicroCFTA.SourceCurrentAllocatedNativeEdgeReturnOrigin

/-!
# Actual checked edge producers before an observed edge finish

The proof descends through partial source traces. A nested producer retains
the original prefix when the enclosing finish continuation is appended.
Both native families start empty at the public initial-query boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceRecursiveIntersectionNative (Shape)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A B : Type}

set_option autoImplicit false

private theorem finish_head
    (control : Control A) (outside : A → Code Symbol Guard B)
    (handle : Nat) (value : EdgeValue Symbol Guard) (rest : Code Symbol Guard B)
    (nonpure : ∀ result, control ≠ .code (.pure result))
    (same : control.bind outside = .code (.finishEdge handle value rest)) :
    ∃ resume, control = .code (.finishEdge handle value resume) ∧ rest = resume.bind outside := by
  cases control with
  | edgeBody => cases same
  | code code =>
      cases code with
      | pure result => exact False.elim (nonpure result rfl)
      | finishEdge original payload resume =>
          change (.code (.finishEdge original payload (resume.bind outside)) : Control B) =
            .code (.finishEdge handle value rest) at same
          obtain ⟨rfl, rfl, tail⟩ := Code.finishEdge.inj (Control.code.inj same)
          exact ⟨resume, rfl, tail.symm⟩
      | fail | work | enter | read | optionalBinder | node | edge | finishNode => cases same

section PrivateProof

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Origin (count : Nat) (control : Control A) (before after : Checked width)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (rest : Code Symbol Guard A) : Prop :=
  ∃ (used bodyCount : Nat) (beforeBody : Checked width)
    (resume : EdgeValue Symbol Guard → Code Symbol Guard A),
    used + bodyCount = count ∧ 0 < used ∧
    Steps used control before
      (.edgeBody request (fun result => .finishEdge handle result (resume result))) beforeBody ∧
    beforeBody.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
    Steps bodyCount (.edgeBody request .pure) beforeBody (.code (.pure value)) after ∧
    resume value = rest ∧
    ∃ (queryUsed : Nat) (queryBefore : Checked width)
      (original : EdgeRequest Symbol Guard)
      (chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      used = queryUsed + 1 ∧
      Steps queryUsed control before (.code (.edge original resume)) queryBefore ∧
      lookupEdge width original queryBefore.native = (handle, chosen) ∧
      demandEdge handle chosen = (.evaluate request, running) ∧
      beforeBody = ⟨running, queryBefore.operations⟩

private theorem origin_prepend {count used handle : Nat}
    {control middle : Control A} {before current after : Checked width}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard} {rest : Code Symbol Guard A}
    (actual : Steps used control before middle current)
    (known : Origin count middle current after handle request value rest) :
    Origin (used + count) control before after handle request value rest := by
  obtain ⟨first, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ := known
  refine ⟨used + first, bodyCount, beforeBody, resume, by omega, by omega,
    actual.trans _ _ _ _ _ _ _ _ entered, owner, bodyTrace, last,
    used + queryUsed, queryBefore, original, chosen, running, by omega, ?_, selected, demanded, stateEq⟩
  exact actual.trans _ _ _ _ _ _ _ _ queryPrefix

private theorem origin_step {count handle : Nat}
    {control middle : Control A} {before current after : Checked width}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard} {rest : Code Symbol Guard A}
    (one : SourceEqualityNativeDemand.step control before = .yielded middle current)
    (known : Origin count middle current after handle request value rest) :
    Origin (count + 1) control before after handle request value rest := by
  have reached : Steps 1 control before middle current := .cons _ _ _ _ _ _ 0 one (.refl _ _)
  simpa only [Nat.add_comm 1 count] using origin_prepend reached known

private theorem origin_bind {count handle : Nat} {control : Control A} {before after : Checked width}
    {request : EdgeRequest Symbol Guard} {value : EdgeValue Symbol Guard} {rest : Code Symbol Guard A}
    (known : Origin count control before after handle request value rest)
    (outside : A → Code Symbol Guard B) :
    Origin count (control.bind outside) before after handle request value (rest.bind outside) := by
  obtain ⟨used, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ := known
  refine ⟨used, bodyCount, beforeBody, fun result => (resume result).bind outside,
    total, positive, ?_, owner, bodyTrace, ?_, ?_⟩
  · have lifted := entered.bind _ _ _ _ _ outside
    simpa only [Control.bind, Code.bind] using lifted
  · change (resume value).bind outside = rest.bind outside
    rw [last]
  · refine ⟨queryUsed, queryBefore, original, chosen, running, counted, ?_, selected, demanded, stateEq⟩
    have lifted := queryPrefix.bind _ _ _ _ _ outside
    simpa only [Control.bind, Code.bind] using lifted

private theorem first_inputs
    {count : Nat} {control final : Control A} {before after : Checked width}
    (actual : Trace count control before final after) (positive : 0 < count) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs control before := by
  cases actual with
  | refl => omega
  | cons _ _ _ _ _ _ _ inputs _ _ => exact inputs

private theorem steps_shape {count : Nat} {control rest : Control A} {before after : Checked width}
    (shape : Shape before.native) (actual : Steps count control before rest after) : Shape after.native := by
  have retained := SourceEqualityNativeDemandMemo.execute_preserves count control before shape
  simpa only [actual.execute, Outcome.state] using retained.1

private def Descent (count : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked width)
    (handle : Nat) (captured : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (rest : Code Symbol Guard A),
    Clean control → Shape before.native →
    Steps count control before (.code (.finishEdge handle value rest)) after →
    after.native.edges.cells handle = some ⟨captured, .evaluating⟩ →
    Origin count control before after handle captured value rest

private theorem descent (count : Nat) : Descent (width := width) count := by
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro A control before after target captured value rest clean shape actual owner
    cases actual with
    | refl => cases clean
    | cons _ _ resume middle _ _ remaining one tail =>
      have currentShape : Shape middle.native := by
        have kept := SourceEqualityNativeDemandMemo.step_preserves control before shape
        simpa only [one, Outcome.state] using kept.1
      have proceed (nextClean : Clean resume) :
          Origin (remaining + 1) control before after target captured value rest :=
        origin_step one (ih remaining (by omega) resume middle after target captured value rest
          nextClean currentShape tail owner)
      cases control with
      | edgeBody request continuation =>
          exact proceed (SourceEqualityNativeDemandBodyCode.body_clean request continuation
            before middle resume one clean)
      | code code =>
        cases code with
        | pure | fail => cases one
        | finishNode | finishEdge => cases clean
        | work job continuation | enter domain left right first second continuation | read name continuation =>
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            exact proceed (clean _)
        | optionalBinder key body continuation =>
            cases chosen : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
            | pending =>
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, chosen, lift] at one
                cases one
            | done result heap =>
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, chosen, lift] at one
                obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
                exact proceed (clean result)
        | node request continuation =>
            cases selected : lookupNode width request before.native with
            | mk selection chosen =>
              cases selection with
              | direct emitted =>
                  have same := Outcome.yielded.inj (by
                    simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, lift] using one)
                  obtain ⟨rfl, rfl⟩ := same
                  exact proceed (bodyCode_bind _ _ (compileNode_bodyCode emitted) clean)
              | memoized handle =>
                cases demanded : demandNode handle chosen with
                | mk observation running =>
                  cases observation with
                  | absent | busy =>
                      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                      cases one
                  | ready result =>
                      have same := Outcome.yielded.inj (by
                        simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                      obtain ⟨rfl, rfl⟩ := same
                      exact proceed (clean result)
                  | evaluate emitted =>
                    have same := Outcome.yielded.inj (by
                      simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                    obtain ⟨rfl, rfl⟩ := same
                    let frame : Value Symbol Guard → Code Symbol Guard A :=
                      fun result => .finishNode handle result (continuation result)
                    rcases steps_bind_cases remaining (.code (compileNode emitted)) frame
                      ⟨running, before.operations⟩ after (.code (.finishEdge target value rest)) tail with
                      ⟨inner, bodyTrace, nonpure, ending⟩ |
                      ⟨bodyCount, frameCount, result, current, total, bodyTrace, frameTrace⟩
                    · obtain ⟨innerRest, head, last⟩ := finish_head inner frame target value rest nonpure ending.symm
                      rw [head] at bodyTrace
                      have nested := ih remaining (by omega) (.code (compileNode emitted))
                        ⟨running, before.operations⟩ after target captured value innerRest
                        (compileNode_bodyCode emitted) currentShape bodyTrace owner
                      have lifted := origin_bind nested frame
                      have reached : Origin remaining (.code ((compileNode emitted).bind frame))
                          ⟨running, before.operations⟩ after target captured value rest := by
                        simpa only [Control.bind, last] using lifted
                      exact origin_step one reached
                    · rcases SourceEqualityNativeDemandProtectedPrefix.finish_node_cases frameCount handle result
                        (continuation result) current after (.code (.finishEdge target value rest)) frameTrace with
                        ⟨zero, ending, finalState⟩ | ⟨suffix, frameTotal, suffixTrace⟩
                      · cases ending
                      · have nextShape := SourceRecursiveIntersectionNative.finishNode_shape handle result current.native
                          (steps_shape currentShape bodyTrace)
                        have nested := ih suffix (by omega) (.code (continuation result))
                          {current with native := SourceRecursiveIntersectionThunks.finishNode handle result current.native}
                          after target captured value rest (clean result) nextShape suffixTrace owner
                        have bodyBound := bodyTrace.bind _ _ _ _ _ frame
                        have finished : Steps 1 (.code (.finishNode handle result (continuation result))) current
                            (.code (continuation result))
                            {current with native := SourceRecursiveIntersectionThunks.finishNode handle result current.native} :=
                          .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
                        have reached := bodyBound.trans _ _ _ _ _ _ _ _ finished
                        have counted : bodyCount + 1 + suffix = remaining := by omega
                        have found : Origin remaining (.code ((compileNode emitted).bind frame))
                            ⟨running, before.operations⟩ after target captured value rest := by
                          simpa only [Control.bind, counted] using origin_prepend reached nested
                        exact origin_step one found
        | edge request continuation =>
            cases selected : lookupEdge width request before.native with
            | mk handle chosen =>
              cases demanded : demandEdge handle chosen with
              | mk observation running =>
                cases observation with
                | absent | busy =>
                    simp only [SourceEqualityNativeDemand.step, selected, demanded] at one
                    cases one
                | ready result =>
                    have same := Outcome.yielded.inj (by
                      simpa only [SourceEqualityNativeDemand.step, selected, demanded] using one)
                    obtain ⟨rfl, rfl⟩ := same
                    exact proceed (clean result)
                | evaluate emitted =>
                  have same := Outcome.yielded.inj (by
                    simpa only [SourceEqualityNativeDemand.step, selected, demanded] using one)
                  obtain ⟨rfl, rfl⟩ := same
                  let frame : EdgeValue Symbol Guard → Code Symbol Guard A :=
                    fun result => .finishEdge handle result (continuation result)
                  rcases steps_bind_cases remaining (.edgeBody emitted .pure) frame
                    ⟨running, before.operations⟩ after (.code (.finishEdge target value rest)) tail with
                    ⟨inner, bodyTrace, nonpure, ending⟩ |
                    ⟨bodyCount, frameCount, result, current, total, bodyTrace, frameTrace⟩
                  · obtain ⟨innerRest, head, last⟩ := finish_head inner frame target value rest nonpure ending.symm
                    rw [head] at bodyTrace
                    have nested := ih remaining (by omega) (.edgeBody emitted .pure)
                      ⟨running, before.operations⟩ after target captured value innerRest
                      (by intro result; trivial) currentShape bodyTrace owner
                    have lifted := origin_bind nested frame
                    have reached : Origin remaining (.edgeBody emitted frame)
                        ⟨running, before.operations⟩ after target captured value rest := by
                      simpa only [Control.bind, Code.bind, last] using lifted
                    exact origin_step one reached
                  · have started := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running emitted demanded).2
                    have retained := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner bodyCount handle emitted
                      ⟨running, before.operations⟩ current result currentShape started bodyTrace
                    rcases SourceEqualityNativeDemandProtectedPrefix.finish_edge_cases frameCount handle result
                      (continuation result) current after (.code (.finishEdge target value rest)) frameTrace with
                      ⟨zero, ending, finalState⟩ | ⟨suffix, frameTotal, suffixTrace⟩
                    · have head := Code.finishEdge.inj (Control.code.inj ending)
                      have requestSame : emitted = captured := by
                        have observed : current.native.edges.cells handle = some ⟨captured, .evaluating⟩ := by
                          simpa only [finalState, head.1] using owner
                        exact congrArg FlatMemoThunk.Cell.request (Option.some.inj (retained.1.symm.trans observed))
                      have found : Origin (remaining + 1) (.code (.edge request continuation)) before current
                          handle emitted result (continuation result) := by
                        exact ⟨1, bodyCount, ⟨running, before.operations⟩, continuation,
                          by omega, by omega, .cons _ _ _ _ _ _ 0 one (.refl _ _), started, bodyTrace, rfl,
                          0, before, request, chosen, running, rfl, .refl _ _, selected, demanded, rfl⟩
                      simpa only [head.1, head.2.1, head.2.2, finalState, requestSame] using found
                    · have nextShape := SourceRecursiveIntersectionNative.finishEdge_shape handle result current.native
                        (steps_shape currentShape bodyTrace)
                      have nested := ih suffix (by omega) (.code (continuation result))
                        {current with native := SourceRecursiveIntersectionThunks.finishEdge handle result current.native}
                        after target captured value rest (clean result) nextShape suffixTrace owner
                      have bodyBound := bodyTrace.bind _ _ _ _ _ frame
                      have finished : Steps 1 (.code (.finishEdge handle result (continuation result))) current
                          (.code (continuation result))
                          {current with native := SourceRecursiveIntersectionThunks.finishEdge handle result current.native} :=
                        .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
                      have reached := bodyBound.trans _ _ _ _ _ _ _ _ finished
                      have counted : bodyCount + 1 + suffix = remaining := by omega
                      have found : Origin remaining (.edgeBody emitted frame)
                          ⟨running, before.operations⟩ after target captured value rest := by
                        simpa only [Control.bind, Code.bind, counted] using origin_prepend reached nested
                      exact origin_step one found


end PrivateProof

/-- Recover the actual edge query event and its same-state isolated dispatch before the observed finish. -/
theorem actual_edge_query_dispatch_from_initial_query_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (originalFuel count handle : Nat) (captured : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) (rest : Code Symbol Guard (Value Symbol Guard))
    (beforeFinish : Checked width)
    (bounded : count < originalFuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishEdge handle row rest)) beforeFinish)
    (owner : beforeFinish.native.edges.cells handle = some ⟨captured, .evaluating⟩) :
    ∃ (queryUsed bodyCount : Nat) (queryBefore beforeBody : Checked width)
      (resume : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      queryUsed + 1 + bodyCount = count ∧ queryUsed < count ∧ queryUsed < originalFuel ∧
      Trace queryUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code (.edge captured resume)) queryBefore ∧
      Trace 1 (.code (.edge captured resume)) queryBefore
        (.edgeBody captured (fun result => .finishEdge handle result (resume result))) beforeBody ∧
      Steps 1 (.code (.edge captured .pure)) queryBefore
        (.edgeBody captured (fun result => .finishEdge handle result (.pure result))) beforeBody ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid queryBefore.native ∧
      EdgeReady queryBefore.native.machine captured ∧
      SourceRecursiveIntersectionEdgeMemo.KeySafe width captured.domain captured.left captured.right ∧
      beforeBody.native.edges.cells handle = some ⟨captured, .evaluating⟩ ∧
      Steps bodyCount (.edgeBody captured .pure) beforeBody (.code (.pure row)) beforeFinish ∧
      resume row = rest := by
  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have clean : Clean (.code (.node rootRequest .pure)) := by
    intro result
    trivial
  obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, _entered, runningOwner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ :=
    descent count (.code (.node rootRequest .pure))
      ⟨initial width machine, operations⟩ beforeFinish handle captured row rest
      clean initialPhysical.shape actual.steps owner
  have splitCount : queryUsed + (count - queryUsed) = count := by omega
  have parts := SourceCurrentHereditaryNativePhysicalSplit.split queryPrefix (splitCount.symm ▸ actual)
  have queryPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension parts.1 initialPhysical).1
  have queryInputs := first_inputs parts.2 (by omega)
  change EdgeReady queryBefore.native.machine original ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width original.domain original.left original.right at queryInputs
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started original captured queryBefore.native chosen running
    handle queryPhysical queryInputs.1 queryInputs.2 selected demanded
  subst original
  have one : SourceEqualityNativeDemand.step (.code (.edge captured resume)) queryBefore =
      .yielded (.edgeBody captured
        (fun result => .finishEdge handle result (resume result))) beforeBody := by
    rw [stateEq]
    simp only [SourceEqualityNativeDemand.step, selected, demanded]
  have isolated : SourceEqualityNativeDemand.step (.code (.edge captured .pure)) queryBefore =
      .yielded (.edgeBody captured
        (fun result => .finishEdge handle result (.pure result))) beforeBody := by
    rw [stateEq]
    simp only [SourceEqualityNativeDemand.step, selected, demanded]
  have actualOne : Trace 1 (.code (.edge captured resume)) queryBefore
      (.edgeBody captured (fun result => .finishEdge handle result (resume result))) beforeBody :=
    .cons _ _ _ _ _ _ 0 queryInputs one (.refl _ _)
  have isolatedOne : Steps 1 (.code (.edge captured .pure)) queryBefore
      (.edgeBody captured (fun result => .finishEdge handle result (.pure result))) beforeBody :=
    .cons _ _ _ _ _ _ 0 isolated (.refl _ _)
  exact ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, by omega, by omega, by omega,
    parts.1, actualOne, isolatedOne, queryPhysical, queryInputs.1, queryInputs.2, runningOwner, bodyTrace, last⟩

end MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceRecursiveIntersectionNative (Shape)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A B : Type}

set_option autoImplicit false

theorem actual_edge_query_dispatch_from_warm_query_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard)
    (before : Checked width)
    (initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (originalFuel count handle : Nat) (captured : EdgeRequest Symbol Guard)
    (row : EdgeValue Symbol Guard) (rest : Code Symbol Guard (Value Symbol Guard))
    (beforeFinish : Checked width)
    (bounded : count < originalFuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      before
      (.code (.finishEdge handle row rest)) beforeFinish)
    (owner : beforeFinish.native.edges.cells handle = some ⟨captured, .evaluating⟩) :
    ∃ (queryUsed bodyCount : Nat) (queryBefore beforeBody : Checked width)
      (resume : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      queryUsed + 1 + bodyCount = count ∧ queryUsed < count ∧ queryUsed < originalFuel ∧
      Trace queryUsed (.code (.node rootRequest .pure))
        before
        (.code (.edge captured resume)) queryBefore ∧
      Trace 1 (.code (.edge captured resume)) queryBefore
        (.edgeBody captured (fun result => .finishEdge handle result (resume result))) beforeBody ∧
      Steps 1 (.code (.edge captured .pure)) queryBefore
        (.edgeBody captured (fun result => .finishEdge handle result (.pure result))) beforeBody ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid queryBefore.native ∧
      EdgeReady queryBefore.native.machine captured ∧
      SourceRecursiveIntersectionEdgeMemo.KeySafe width captured.domain captured.left captured.right ∧
      beforeBody.native.edges.cells handle = some ⟨captured, .evaluating⟩ ∧
      Steps bodyCount (.edgeBody captured .pure) beforeBody (.code (.pure row)) beforeFinish ∧
      resume row = rest
 := by
  have clean : Clean (.code (.node rootRequest .pure)) := by
    intro result
    trivial
  obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, _entered, runningOwner, bodyTrace, last,
    queryUsed, queryBefore, original, chosen, running, counted, queryPrefix, selected, demanded, stateEq⟩ :=
    descent count (.code (.node rootRequest .pure))
      before beforeFinish handle captured row rest
      clean initialPhysical.shape actual.steps owner
  have splitCount : queryUsed + (count - queryUsed) = count := by omega
  have parts := SourceCurrentHereditaryNativePhysicalSplit.split queryPrefix (splitCount.symm ▸ actual)
  have queryPhysical := (SourceCurrentNativeEnterCommonOperand.checked_trace_extension parts.1 initialPhysical).1
  have queryInputs := first_inputs parts.2 (by omega)
  change EdgeReady queryBefore.native.machine original ∧
    SourceRecursiveIntersectionEdgeMemo.KeySafe width original.domain original.left original.right at queryInputs
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started original captured queryBefore.native chosen running
    handle queryPhysical queryInputs.1 queryInputs.2 selected demanded
  subst original
  have one : SourceEqualityNativeDemand.step (.code (.edge captured resume)) queryBefore =
      .yielded (.edgeBody captured
        (fun result => .finishEdge handle result (resume result))) beforeBody := by
    rw [stateEq]
    simp only [SourceEqualityNativeDemand.step, selected, demanded]
  have isolated : SourceEqualityNativeDemand.step (.code (.edge captured .pure)) queryBefore =
      .yielded (.edgeBody captured
        (fun result => .finishEdge handle result (.pure result))) beforeBody := by
    rw [stateEq]
    simp only [SourceEqualityNativeDemand.step, selected, demanded]
  have actualOne : Trace 1 (.code (.edge captured resume)) queryBefore
      (.edgeBody captured (fun result => .finishEdge handle result (resume result))) beforeBody :=
    .cons _ _ _ _ _ _ 0 queryInputs one (.refl _ _)
  have isolatedOne : Steps 1 (.code (.edge captured .pure)) queryBefore
      (.edgeBody captured (fun result => .finishEdge handle result (.pure result))) beforeBody :=
    .cons _ _ _ _ _ _ 0 isolated (.refl _ _)
  exact ⟨queryUsed, bodyCount, queryBefore, beforeBody, resume, by omega, by omega, by omega,
    parts.1, actualOne, isolatedOne, queryPhysical, queryInputs.1, queryInputs.2, runningOwner, bodyTrace, last⟩

end MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin
