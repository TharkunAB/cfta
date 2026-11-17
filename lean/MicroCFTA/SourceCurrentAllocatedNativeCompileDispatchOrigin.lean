import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
import MicroCFTA.SourceEqualityNativeDemandMemo
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

/-!
# Actual compiled producers before an observed node finish

The proof descends through partial source traces. A nested producer retains
the original prefix when the enclosing finish continuation is appended.
Both native families start empty at the public initial-query boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
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
    (handle : Nat) (value : Value Symbol Guard) (rest : Code Symbol Guard B)
    (nonpure : ∀ result, control ≠ .code (.pure result))
    (same : control.bind outside = .code (.finishNode handle value rest)) :
    ∃ resume, control = .code (.finishNode handle value resume) ∧ rest = resume.bind outside := by
  cases control with
  | edgeBody => cases same
  | code code =>
      cases code with
      | pure result => exact False.elim (nonpure result rfl)
      | finishNode original payload resume =>
          change (.code (.finishNode original payload (resume.bind outside)) : Control B) =
            .code (.finishNode handle value rest) at same
          obtain ⟨rfl, rfl, tail⟩ := Code.finishNode.inj (Control.code.inj same)
          exact ⟨resume, rfl, tail.symm⟩
      | fail | work | enter | read | optionalBinder | node | edge | finishEdge => cases same

section PrivateProof

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def Origin (count : Nat) (control : Control A) (before after : Checked width)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Code Symbol Guard A) : Prop :=
  ∃ (used bodyCount : Nat) (beforeBody : Checked width)
    (resume : Value Symbol Guard → Code Symbol Guard A),
    used + bodyCount = count ∧ 0 < used ∧
    Steps used control before
      (.code ((compileNode request).bind (fun result => .finishNode handle result (resume result)))) beforeBody ∧
    beforeBody.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
    Steps bodyCount (.code (compileNode request)) beforeBody (.code (.pure value)) after ∧
    resume value = rest

private theorem origin_prepend {count used handle : Nat}
    {control middle : Control A} {before current after : Checked width}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard} {rest : Code Symbol Guard A}
    (actual : Steps used control before middle current)
    (known : Origin count middle current after handle request value rest) :
    Origin (used + count) control before after handle request value rest := by
  obtain ⟨first, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last⟩ := known
  exact ⟨used + first, bodyCount, beforeBody, resume, by omega, by omega,
    actual.trans _ _ _ _ _ _ _ _ entered, owner, bodyTrace, last⟩

private theorem origin_step {count handle : Nat}
    {control middle : Control A} {before current after : Checked width}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard} {rest : Code Symbol Guard A}
    (one : SourceEqualityNativeDemand.step control before = .yielded middle current)
    (known : Origin count middle current after handle request value rest) :
    Origin (count + 1) control before after handle request value rest := by
  have reached : Steps 1 control before middle current := .cons _ _ _ _ _ _ 0 one (.refl _ _)
  simpa only [Nat.add_comm 1 count] using origin_prepend reached known

private theorem origin_bind {count handle : Nat} {control : Control A} {before after : Checked width}
    {request : NodeRequest Symbol Guard} {value : Value Symbol Guard} {rest : Code Symbol Guard A}
    (known : Origin count control before after handle request value rest)
    (outside : A → Code Symbol Guard B) :
    Origin count (control.bind outside) before after handle request value (rest.bind outside) := by
  obtain ⟨used, bodyCount, beforeBody, resume, total, positive, entered, owner, bodyTrace, last⟩ := known
  refine ⟨used, bodyCount, beforeBody, fun result => (resume result).bind outside,
    total, positive, ?_, owner, bodyTrace, ?_⟩
  · have lifted := entered.bind _ _ _ _ _ outside
    simpa only [Control.bind, Code.bind_assoc, Code.bind] using lifted
  · change (resume value).bind outside = rest.bind outside
    rw [last]

private theorem steps_shape {count : Nat} {control rest : Control A} {before after : Checked width}
    (shape : Shape before.native) (actual : Steps count control before rest after) : Shape after.native := by
  have retained := SourceEqualityNativeDemandMemo.execute_preserves count control before shape
  simpa only [actual.execute, Outcome.state] using retained.1

private def Descent (count : Nat) : Prop :=
  ∀ {A : Type} (control : Control A) (before after : Checked width)
    (handle : Nat) (captured : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (rest : Code Symbol Guard A),
    Clean control → Shape before.native →
    Steps count control before (.code (.finishNode handle value rest)) after →
    after.native.nodes.cells handle = some ⟨captured, .evaluating⟩ →
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
                      ⟨running, before.operations⟩ after (.code (.finishNode target value rest)) tail with
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
                    · have started := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running emitted demanded).2
                      have retained := SourceEqualityNativeDemandProtectedPrefix.node_body_owner bodyCount handle emitted
                        ⟨running, before.operations⟩ current result currentShape started bodyTrace
                      rcases SourceEqualityNativeDemandProtectedPrefix.finish_node_cases frameCount handle result
                        (continuation result) current after (.code (.finishNode target value rest)) frameTrace with
                        ⟨zero, ending, finalState⟩ | ⟨suffix, frameTotal, suffixTrace⟩
                      · have head := Code.finishNode.inj (Control.code.inj ending)
                        have requestSame : emitted = captured := by
                          have observed : current.native.nodes.cells handle = some ⟨captured, .evaluating⟩ := by
                            simpa only [finalState, head.1] using owner
                          exact congrArg FlatMemoThunk.Cell.request (Option.some.inj (retained.1.symm.trans observed))
                        have found : Origin (remaining + 1) (.code (.node request continuation)) before current
                            handle emitted result (continuation result) := by
                          exact ⟨1, bodyCount, ⟨running, before.operations⟩, continuation,
                            by omega, by omega, .cons _ _ _ _ _ _ 0 one (.refl _ _), started, bodyTrace, rfl⟩
                        simpa only [head.1, head.2.1, head.2.2, finalState, requestSame] using found
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
                    ⟨running, before.operations⟩ after (.code (.finishNode target value rest)) tail with
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
                  · rcases SourceEqualityNativeDemandProtectedPrefix.finish_edge_cases frameCount handle result
                      (continuation result) current after (.code (.finishNode target value rest)) frameTrace with
                      ⟨zero, ending, finalState⟩ | ⟨suffix, frameTotal, suffixTrace⟩
                    · cases ending
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

/-- The observed node finish has an actual compiled producer in the same original query trace. -/
theorem compiled_node_origin_from_initial_query_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (originalFuel count handle : Nat) (captured : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) (rest : Code Symbol Guard (Value Symbol Guard))
    (beforeFinish : Checked width)
    (bounded : count < originalFuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)
      (.code (.finishNode handle value rest)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨captured, .evaluating⟩) :
    ∃ (dispatchUsed bodyCount : Nat) (beforeBody : Checked width)
      (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      dispatchUsed + bodyCount = count ∧ 0 < dispatchUsed ∧ dispatchUsed < originalFuel ∧
      Steps dispatchUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code ((compileNode captured).bind
          (fun result => .finishNode handle result (resume result)))) beforeBody ∧
      beforeBody.native.nodes.cells handle = some ⟨captured, .evaluating⟩ ∧
      Steps bodyCount (.code (compileNode captured)) beforeBody (.code (.pure value)) beforeFinish ∧
      resume value = rest := by
  have initialValid := SourceRecursiveIntersectionThunks.initial_valid width
    SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin machine machineValid
  have initialShape := SourceRecursiveIntersectionNative.shape_of_valid
    SourceEqualityConstraintConstructors.top SourceEqualityPCSNativeEdge.conjoin _ initialValid
  have clean : Clean (.code (.node rootRequest .pure)) := by
    intro result
    trivial
  obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, entered, running, bodyTrace, last⟩ :=
    descent count (.code (.node rootRequest .pure))
      ⟨initial width machine, operations⟩ beforeFinish handle captured value rest
      clean initialShape actual.steps owner
  exact ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, by omega,
    entered, running, bodyTrace, last⟩

end MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin

namespace MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
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

/- Note [Actual warm query prefix]
The producer descent already accepts a clean control and a shaped native
state. Empty initialization is one way to obtain those past facts.
An actual warm start also supplies them. Keep its full tables and exact
start state when exposing the same producer and actual-prefix induction.
The induction receives initial cache laws and derives later cache laws
from its genuine finish callbacks. It adds no source semantic claim.
-/

theorem compiled_node_origin_from_warm_query_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard)
    (start : Checked width) (startShape : Shape start.native)
    (originalFuel count handle : Nat) (captured : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) (rest : Code Symbol Guard (Value Symbol Guard))
    (beforeFinish : Checked width)
    (bounded : count < originalFuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      start
      (.code (.finishNode handle value rest)) beforeFinish)
    (owner : beforeFinish.native.nodes.cells handle = some ⟨captured, .evaluating⟩) :
    ∃ (dispatchUsed bodyCount : Nat) (beforeBody : Checked width)
      (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      dispatchUsed + bodyCount = count ∧ 0 < dispatchUsed ∧ dispatchUsed < originalFuel ∧
      Steps dispatchUsed (.code (.node rootRequest .pure))
        start
        (.code ((compileNode captured).bind
          (fun result => .finishNode handle result (resume result)))) beforeBody ∧
      beforeBody.native.nodes.cells handle = some ⟨captured, .evaluating⟩ ∧
      Steps bodyCount (.code (compileNode captured)) beforeBody (.code (.pure value)) beforeFinish ∧
      resume value = rest
 := by
  have clean : Clean (.code (.node rootRequest .pure)) := by
    intro result
    trivial
  obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, entered, running, bodyTrace, last⟩ :=
    descent count (.code (.node rootRequest .pure)) start beforeFinish handle captured value rest
      clean startShape actual.steps owner
  exact ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, by omega,
    entered, running, bodyTrace, last⟩

end MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
