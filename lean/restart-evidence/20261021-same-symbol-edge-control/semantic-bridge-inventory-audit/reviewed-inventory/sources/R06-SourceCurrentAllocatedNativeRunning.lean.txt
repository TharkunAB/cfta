import MicroCFTA.SourceEqualityNativeDemandRunning
import MicroCFTA.SourceRecursiveIntersectionNativeIdle

/-!
# Completed checked bodies leave no new running cells

The proof follows actual checked traces. An edge prefix keeps the native
state. Each nested source request finishes only the handle that it started.
No old native execution or language receipt is used. Semantic completion
of general recursive checked bodies remains a separate obligation.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRunning
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceRecursiveIntersectionNative (Shape Retains Idle ActiveAbove)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State

private theorem node_finish_before (handle : Nat) (request : NodeRequest Symbol Guard)
    (chosen current middle : Native width Symbol Guard) (value : Value Symbol Guard)
    (demand : demandNode handle chosen = (.evaluate request, current)) (body : Retains middle current) :
    Retains (SourceRecursiveIntersectionThunks.finishNode handle value middle) chosen := by
  constructor
  · intro other original running
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle value middle.nodes original running
    have atBody := (SourceRecursiveIntersectionNative.finishNode_running_before handle value middle).1 other original running
    exact SourceRecursiveIntersectionNative.demandNode_running_before_other handle other chosen current _ demand
      original different (body.1 other original atBody)
  · intro other original running
    have atBody := body.2 other original running
    have same : chosen.edges = current.edges := congrArg (fun actual => actual.2.edges) demand
    rw [← same] at atBody
    exact atBody

private theorem edge_finish_before (handle : Nat) (request : EdgeRequest Symbol Guard)
    (chosen current middle : Native width Symbol Guard) (value : EdgeValue Symbol Guard)
    (demand : demandEdge handle chosen = (.evaluate request, current)) (body : Retains middle current) :
    Retains (SourceRecursiveIntersectionThunks.finishEdge handle value middle) chosen := by
  constructor
  · intro other original running
    have atBody := body.1 other original running
    have same : chosen.nodes = current.nodes := congrArg (fun actual => actual.2.nodes) demand
    rw [← same] at atBody
    exact atBody
  · intro other original running
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle value middle.edges original running
    have atBody := (SourceRecursiveIntersectionNative.finishEdge_running_before handle value middle).2 other original running
    exact SourceRecursiveIntersectionNative.demandEdge_running_before_other handle other chosen current _ demand
      original different (body.2 other original atBody)

/-- Every running cell after a completed clean checked trace was already running before that trace. -/
theorem trace_running_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) {Output : Type} (control : Control Output) (before after : State width) (value : Output)
    (trace : Steps fuel control before (.code (.pure value)) after) :
    Clean control → Shape before.native → Retains after.native before.native := by
  induction fuel using Nat.strongRecOn generalizing Output control before after value with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          obtain ⟨same, retained⟩ := steps_zero _ _ _ _ trace
          subst control
          subst after
          exact fun _ _ => Retains.refl _
      | succ fuel =>
          obtain ⟨rest, current, one, tail⟩ := steps_succ fuel _ _ _ _ trace
          cases control with
          | edgeBody request next =>
              intro clean shape
              have restClean := SourceEqualityNativeDemandBodyCode.body_clean request next before current rest one clean
              have same : current.native = before.native := by
                simpa only [show body request next before = .yielded rest current from one, Outcome.state] using
                  SourceEqualityNativeDemandOperations.body_native request next before
              have currentShape : Shape current.native := by rw [same]; exact shape
              have completed := ih fuel (by omega) rest current after value tail restClean currentShape
              simpa only [same] using completed
          | code code =>
              cases code with
              | pure | fail => cases one
              | finishNode | finishEdge => intro clean; cases clean
              | work job next | enter domain left right first second next | read name next =>
                  have same := Outcome.yielded.inj one
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  intro clean shape
                  have finished := ih fuel (by omega) _ _ _ _ tail (clean _) shape
                  exact finished
              | optionalBinder pair body next =>
                  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
                  | pending =>
                      simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                      cases one
                  | done result heap =>
                      simp only [step, SourceRecursiveIntersectionNative.step, actual, lift] at one
                      have same := Outcome.yielded.inj one
                      rcases same.1 with rfl
                      rcases same.2 with rfl
                      intro clean shape
                      have finished := ih fuel (by omega) _ _ _ _ tail (clean _) shape
                      exact finished
              | node request next =>
                  cases selected : lookupNode width request before.native with
                  | mk selection chosen =>
                      cases selection with
                      | direct actual =>
                          simp only [step, SourceRecursiveIntersectionNative.step, selected, lift] at one
                          have same := Outcome.yielded.inj one
                          rcases same.1 with rfl
                          rcases same.2 with rfl
                          obtain ⟨inner, outer, result, middle, count, bodyTrace, restTrace⟩ := steps_bind_inverse fuel
                            (.code (compileNode actual)) next ⟨chosen, before.operations⟩ after value tail
                          intro clean shape
                          have chosenShape : Shape chosen := by
                            simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_shape request before.native shape
                          have middleShape := (SourceEqualityNativeDemandRunning.trace_retains inner _ _ _ _ bodyTrace
                            (SourceRecursiveIntersectionCode.compileNode_bodyCode actual) chosenShape).1
                          have bodyBefore := ih inner (by omega) _ _ _ _ bodyTrace (compileNode_bodyCode actual) chosenShape
                          have tailBefore := ih outer (by omega) _ _ _ _ restTrace (clean result) middleShape
                          have published : Retains chosen before.native := by
                            simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_running_before request before.native
                          exact tailBefore.trans (bodyBefore.trans published)
                      | memoized handle =>
                          cases demanded : demandNode handle chosen with
                          | mk observation running =>
                              cases observation with
                              | absent | busy =>
                                  simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                                  cases one
                              | ready result =>
                                  simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                                  have same := Outcome.yielded.inj one
                                  rcases same.1 with rfl
                                  rcases same.2 with rfl
                                  intro clean shape
                                  have chosenShape : Shape chosen := by
                                    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_shape request before.native shape
                                  have unchanged := (SourceRecursiveIntersectionNative.demandNode_ready handle chosen running result demanded).choose_spec.2
                                  have runningShape : Shape running := by rw [unchanged]; exact chosenShape
                                  have tailBefore := ih fuel (by omega) _ _ _ _ tail (clean result) runningShape
                                  have published : Retains chosen before.native := by
                                    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_running_before request before.native
                                  rw [unchanged] at tailBefore
                                  exact tailBefore.trans published
                              | evaluate actual =>
                                  simp only [step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                                  have same := Outcome.yielded.inj one
                                  rcases same.1 with rfl
                                  rcases same.2 with rfl
                                  obtain ⟨inner, outer, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
                                    (.code (compileNode actual)) (fun result => .finishNode handle result (next result))
                                    ⟨running, before.operations⟩ after value tail
                                  obtain ⟨remaining, frameCount, restTrace⟩ := SourceEqualityNativeDemandNodeReadback.finish_trace
                                    outer handle result (next result) middle after value frameTrace
                                  intro clean shape
                                  have chosenShape : Shape chosen := by
                                    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_shape request before.native shape
                                  have runningShape : Shape running := by
                                    simpa only [demanded] using SourceRecursiveIntersectionNative.demandNode_shape handle chosen chosenShape
                                  have middleShape := (SourceEqualityNativeDemandRunning.trace_retains inner _ _ _ _ bodyTrace
                                    (compileNode_bodyCode actual) runningShape).1
                                  have bodyBefore := ih inner (by omega) _ _ _ _ bodyTrace (compileNode_bodyCode actual) runningShape
                                  have tailBefore := ih remaining (by omega) _ _ _ _ restTrace (clean result)
                                    (SourceRecursiveIntersectionNative.finishNode_shape handle result middle.native middleShape)
                                  have restored := node_finish_before handle actual chosen running middle.native result demanded bodyBefore
                                  have published : Retains chosen before.native := by
                                    simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_running_before request before.native
                                  exact tailBefore.trans (restored.trans published)
              | edge request next =>
                  cases selected : lookupEdge width request before.native with
                  | mk handle chosen =>
                      cases demanded : demandEdge handle chosen with
                      | mk observation running =>
                          cases observation with
                          | absent | busy => simp only [step, selected, demanded] at one; cases one
                          | ready result =>
                              simp only [step, selected, demanded] at one
                              have same := Outcome.yielded.inj one
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              intro clean shape
                              have chosenShape : Shape chosen := by
                                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_shape request before.native shape
                              have unchanged := (SourceRecursiveIntersectionNative.demandEdge_ready handle chosen running result demanded).choose_spec.2
                              have runningShape : Shape running := by rw [unchanged]; exact chosenShape
                              have tailBefore := ih fuel (by omega) _ _ _ _ tail (clean result) runningShape
                              have published : Retains chosen before.native := by
                                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_running_before request before.native
                              rw [unchanged] at tailBefore
                              exact tailBefore.trans published
                          | evaluate actual =>
                              simp only [step, selected, demanded] at one
                              have same := Outcome.yielded.inj one
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              obtain ⟨inner, outer, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
                                (.edgeBody actual .pure) (fun result => .finishEdge handle result (next result))
                                ⟨running, before.operations⟩ after value tail
                              obtain ⟨remaining, frameCount, restTrace⟩ := SourceEqualityNativeDemandRunning.finish_edge_trace
                                outer handle result (next result) middle after value frameTrace
                              intro clean shape
                              have chosenShape : Shape chosen := by
                                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_shape request before.native shape
                              have runningShape : Shape running := by
                                simpa only [demanded] using SourceRecursiveIntersectionNative.demandEdge_shape handle chosen chosenShape
                              have middleShape := (SourceEqualityNativeDemandRunning.trace_retains inner _ _ _ _ bodyTrace
                                (by intro value; trivial) runningShape).1
                              have bodyBefore := ih inner (by omega) _ _ _ _ bodyTrace (by intro value; trivial) runningShape
                              have tailBefore := ih remaining (by omega) _ _ _ _ restTrace (clean result)
                                (SourceRecursiveIntersectionNative.finishEdge_shape handle result middle.native middleShape)
                              have restored := edge_finish_before handle actual chosen running middle.native result demanded bodyBefore
                              have published : Retains chosen before.native := by
                                simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_running_before request before.native
                              exact tailBefore.trans (restored.trans published)

/-- A completed checked run leaves no running cell that was absent before its source body. -/
theorem done_running_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before after : State width) (value : Output)
    (done : execute fuel control before = .done value after) (clean : Clean control) (shape : Shape before.native) :
    Retains after.native before.native := by
  obtain ⟨count, _, trace⟩ := done_trace fuel control before after value done
  exact trace_running_before count control before after value trace clean shape

/-- A completed checked source body returns idle native tables from idle native tables. -/
theorem done_idle [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before after : State width) (value : Output)
    (clean : Clean control) (shape : Shape before.native) (idle : Idle before.native)
    (done : execute fuel control before = .done value after) : Idle after.native :=
  idle.retained (done_running_before fuel control before after value done clean shape)

/-- A checked node body and its own finish restore the cells from before that node demand. -/
theorem node_body_finish_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (chosen : Native width Symbol Guard)
    (before after : State width) (value : Value Symbol Guard)
    (demand : demandNode handle chosen = (.evaluate request, before.native)) (shape : Shape before.native)
    (body : Steps fuel (.code (compileNode request)) before (.code (.pure value)) after) :
    Retains (SourceRecursiveIntersectionThunks.finishNode handle value after.native) chosen :=
  node_finish_before handle request chosen before.native after.native value demand
    (trace_running_before fuel _ before after value body (compileNode_bodyCode request) shape)

/-- A checked edge body and its own finish restore the cells from before that edge demand. -/
theorem edge_body_finish_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (request : EdgeRequest Symbol Guard) (chosen : Native width Symbol Guard)
    (before after : State width) (value : EdgeValue Symbol Guard)
    (demand : demandEdge handle chosen = (.evaluate request, before.native)) (shape : Shape before.native)
    (body : Steps fuel (.edgeBody request .pure) before (.code (.pure value)) after) :
    Retains (SourceRecursiveIntersectionThunks.finishEdge handle value after.native) chosen :=
  edge_finish_before handle request chosen before.native after.native value demand
    (trace_running_before fuel _ before after value body (by intro value; trivial) shape)

/-- Actual checked node completion restores the caller's stronger semantic request bound. -/
theorem node_finish_active [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (chosen : Native width Symbol Guard)
    (before after : State width) (value : Value Symbol Guard) (active : ActiveAbove view holds bound chosen)
    (demand : demandNode handle chosen = (.evaluate request, before.native)) (shape : Shape before.native)
    (body : Steps fuel (.code (compileNode request)) before (.code (.pure value)) after) :
    ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.finishNode handle value after.native) :=
  active.running_before view holds bound chosen _
    (node_body_finish_before fuel handle request chosen before after value demand shape body)

/-- Actual checked edge completion restores the caller's stronger semantic request bound. -/
theorem edge_finish_active [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (fuel handle : Nat) (request : EdgeRequest Symbol Guard) (chosen : Native width Symbol Guard)
    (before after : State width) (value : EdgeValue Symbol Guard) (active : ActiveAbove view holds bound chosen)
    (demand : demandEdge handle chosen = (.evaluate request, before.native)) (shape : Shape before.native)
    (body : Steps fuel (.edgeBody request .pure) before (.code (.pure value)) after) :
    ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.finishEdge handle value after.native) :=
  active.running_before view holds bound chosen _
    (edge_body_finish_before fuel handle request chosen before after value demand shape body)

end MicroCFTA.SourceCurrentAllocatedNativeRunning
