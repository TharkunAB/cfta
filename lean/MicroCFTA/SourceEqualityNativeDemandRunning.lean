import MicroCFTA.SourceEqualityNativeDemandBodyCode
import MicroCFTA.SourceEqualityNativeDemandNodeReadback
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Checked source bodies retain enclosing running cells

Strong induction splits actual completed traces at nested bodies and their
finish frames. Each nested request can finish only its own started handle.
Checked edge-prefix execution remains part of the actual trace. No old
eager completion, semantic receipt, or future valid state is assumed.
-/
namespace MicroCFTA.SourceEqualityNativeDemandRunning
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityNativeDemandBodyCode (Clean)
open SourceRecursiveIntersectionNative (Shape Retains lookupNode_shape lookupEdge_shape demandNode_shape demandEdge_shape
  lookupNode_retains lookupEdge_retains demandNode_retains demandEdge_retains finishNode_shape finishEdge_shape
  demandNode_evaluate demandEdge_evaluate)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- An edge finish frame consumes exactly one actual step at its updated full state. -/
theorem finish_edge_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (handle : Nat) (result : EdgeValue Symbol Guard) (next : Code Symbol Guard Output)
    (before after : State width) (value : Output)
    (trace : Steps fuel (.code (.finishEdge handle result next)) before (.code (.pure value)) after) :
    ∃ rest, fuel = rest + 1 ∧ Steps rest (.code next)
      {before with native := SourceRecursiveIntersectionThunks.finishEdge handle result before.native}
      (.code (.pure value)) after := by
  cases fuel with
  | zero => cases (steps_zero _ _ _ _ trace).1
  | succ fuel =>
      obtain ⟨control, current, one, tail⟩ := steps_succ fuel _ _ _ _ trace
      have same := Outcome.yielded.inj one
      rcases same.1 with rfl
      rcases same.2 with rfl
      exact ⟨fuel, rfl, tail⟩

/-- Actual completed source traces retain memo structure and every enclosing running request. -/
theorem trace_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) {Output : Type} (control : Control Output) (before after : State width) (value : Output)
    (trace : Steps fuel control before (.code (.pure value)) after) :
    Clean control → Shape before.native → Shape after.native ∧ Retains before.native after.native := by
  induction fuel using Nat.strongRecOn generalizing Output control before after value with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          obtain ⟨same, retained⟩ := steps_zero _ _ _ _ trace
          subst control
          subst after
          intro _ shape
          exact ⟨shape, Retains.refl _⟩
      | succ fuel =>
          obtain ⟨rest, current, one, tail⟩ := steps_succ fuel _ _ _ _ trace
          cases control with
          | edgeBody request next =>
              intro clean shape
              have restClean := SourceEqualityNativeDemandBodyCode.body_clean request next before current rest one clean
              have currentNative : current.native = before.native := by
                have same := SourceEqualityNativeDemandOperations.body_native request next before
                simpa only [show body request next before = .yielded rest current from one, Outcome.state] using same
              have currentShape : Shape current.native := by rw [currentNative]; exact shape
              have finished := ih fuel (by omega) rest current after value tail restClean currentShape
              simpa only [currentNative] using finished
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
                          have chosenShape : Shape chosen := by simpa only [selected] using lookupNode_shape request before.native shape
                          have entered : Retains before.native chosen := by simpa only [selected] using lookupNode_retains request before.native shape
                          have built := ih inner (by omega) _ _ _ _ bodyTrace (compileNode_bodyCode actual) chosenShape
                          have finished := ih outer (by omega) _ _ _ _ restTrace (clean result) built.1
                          exact ⟨finished.1, entered.trans (built.2.trans finished.2)⟩
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
                                  have chosenShape : Shape chosen := by simpa only [selected] using lookupNode_shape request before.native shape
                                  have currentShape : Shape running := by simpa only [demanded] using demandNode_shape handle chosen chosenShape
                                  have published : Retains before.native chosen := by simpa only [selected] using lookupNode_retains request before.native shape
                                  have started : Retains chosen running := by simpa only [demanded] using demandNode_retains handle chosen
                                  have finished := ih fuel (by omega) _ _ _ _ tail (clean result) currentShape
                                  exact ⟨finished.1, published.trans (started.trans finished.2)⟩
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
                                  have chosenShape : Shape chosen := by simpa only [selected] using lookupNode_shape request before.native shape
                                  have currentShape : Shape running := by simpa only [demanded] using demandNode_shape handle chosen chosenShape
                                  have published : Retains before.native chosen := by simpa only [selected] using lookupNode_retains request before.native shape
                                  have started : Retains chosen running := by simpa only [demanded] using demandNode_retains handle chosen
                                  have entered := published.trans started
                                  have built := ih inner (by omega) _ _ _ _ bodyTrace (compileNode_bodyCode actual) currentShape
                                  have finished := ih remaining (by omega) _ _ _ _ restTrace (clean result) (finishNode_shape handle result middle.native built.1)
                                  refine ⟨finished.1, ?_, ?_⟩
                                  · intro other original runningCell
                                    have beforeDemand := published.1 other original runningCell
                                    have suspended := (demandNode_evaluate handle chosen running actual demanded).1
                                    have different : other ≠ handle := by
                                      intro same
                                      subst other
                                      have impossible := Option.some.inj (beforeDemand.symm.trans suspended)
                                      cases impossible
                                    have inBody := built.2.1 other original (entered.1 other original runningCell)
                                    exact finished.2.1 other original (FlatMemoThunk.finish_running_other handle other result middle.native.nodes original different inBody)
                                  · intro other original runningCell
                                    exact finished.2.2 other original (built.2.2 other original (entered.2 other original runningCell))
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
                              have chosenShape : Shape chosen := by simpa only [selected] using lookupEdge_shape request before.native shape
                              have currentShape : Shape running := by simpa only [demanded] using demandEdge_shape handle chosen chosenShape
                              have published : Retains before.native chosen := by simpa only [selected] using lookupEdge_retains request before.native shape
                              have started : Retains chosen running := by simpa only [demanded] using demandEdge_retains handle chosen
                              have finished := ih fuel (by omega) _ _ _ _ tail (clean result) currentShape
                              exact ⟨finished.1, published.trans (started.trans finished.2)⟩
                          | evaluate actual =>
                              simp only [step, selected, demanded] at one
                              have same := Outcome.yielded.inj one
                              rcases same.1 with rfl
                              rcases same.2 with rfl
                              obtain ⟨inner, outer, result, middle, count, bodyTrace, frameTrace⟩ := steps_bind_inverse fuel
                                (.edgeBody actual .pure) (fun result => .finishEdge handle result (next result))
                                ⟨running, before.operations⟩ after value tail
                              obtain ⟨remaining, frameCount, restTrace⟩ := finish_edge_trace outer handle result (next result) middle after value frameTrace
                              intro clean shape
                              have chosenShape : Shape chosen := by simpa only [selected] using lookupEdge_shape request before.native shape
                              have currentShape : Shape running := by simpa only [demanded] using demandEdge_shape handle chosen chosenShape
                              have published : Retains before.native chosen := by simpa only [selected] using lookupEdge_retains request before.native shape
                              have started : Retains chosen running := by simpa only [demanded] using demandEdge_retains handle chosen
                              have entered := published.trans started
                              have built := ih inner (by omega) _ _ _ _ bodyTrace (by intro value; trivial) currentShape
                              have finished := ih remaining (by omega) _ _ _ _ restTrace (clean result) (finishEdge_shape handle result middle.native built.1)
                              refine ⟨finished.1, ?_, ?_⟩
                              · intro other original runningCell
                                exact finished.2.1 other original (built.2.1 other original (entered.1 other original runningCell))
                              · intro other original runningCell
                                have beforeDemand := published.2 other original runningCell
                                have suspended := (demandEdge_evaluate handle chosen running actual demanded).1
                                have different : other ≠ handle := by
                                  intro same
                                  subst other
                                  have impossible := Option.some.inj (beforeDemand.symm.trans suspended)
                                  cases impossible
                                have inBody := built.2.2 other original (entered.2 other original runningCell)
                                exact finished.2.2 other original (FlatMemoThunk.finish_running_other handle other result middle.native.edges original different inBody)

/-- Every actual completed clean source run retains both memo structures and original running cells. -/
theorem done_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before after : State width) (value : Output)
    (done : execute fuel control before = .done value after) (clean : Clean control) (shape : Shape before.native) :
    Shape after.native ∧ Retains before.native after.native := by
  obtain ⟨count, _, trace⟩ := done_trace fuel control before after value done
  exact trace_retains count control before after value trace clean shape

/-- An actual compiled node body preserves its original evaluating cell for its own completion frame. -/
theorem node_body_cell [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (before after : State width) (value : Value Symbol Guard)
    (shape : Shape before.native) (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (done : execute fuel (.code (compileNode request)) before = .done value after) :
    after.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value after.native).nodes.cells handle = some ⟨request, .returned value⟩ := by
  have retained := done_retains fuel _ before after value done (compileNode_bodyCode request) shape
  have present := retained.2.1 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.native.nodes request present⟩

/-- An actual checked edge body preserves its original evaluating cell for its own completion frame. -/
theorem edge_body_cell [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel handle : Nat) (request : EdgeRequest Symbol Guard) (before after : State width) (value : EdgeValue Symbol Guard)
    (shape : Shape before.native) (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (done : execute fuel (.edgeBody request .pure) before = .done value after) :
    after.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishEdge handle value after.native).edges.cells handle = some ⟨request, .returned value⟩ := by
  have retained := done_retains fuel _ before after value done (by intro value; trivial) shape
  have present := retained.2.2 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.native.edges request present⟩

end MicroCFTA.SourceEqualityNativeDemandRunning
