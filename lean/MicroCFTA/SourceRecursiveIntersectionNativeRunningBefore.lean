import MicroCFTA.FlatMemoThunkRunningBefore
import MicroCFTA.SourceRecursiveIntersectionNativeRunning
import MicroCFTA.SourceRecursiveIntersectionNativeObservations

/-!
# Completed source bodies leave no new running request

Actual publication creates suspended cells. Each completed nested source
request finishes its own running cell. Every running cell after a completed
source body was already running before that body.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual node publication cannot create a running request in either memo family. -/
theorem lookupNode_running_before (request : NodeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains (lookupNode width request state).2 state := by
  cases requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, requested] using Retains.refl state
  | some key =>
      exact ⟨by simpa only [lookupNode, requested] using FlatMemoThunk.lookup_running_before key request state.nodes,
        by simpa only [lookupNode, requested] using FlatMemoThunk.Running.refl state.edges⟩

/-- Actual edge publication cannot create a running request in either memo family. -/
theorem lookupEdge_running_before (request : EdgeRequest Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains (lookupEdge width request state).2 state :=
  ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.lookup_running_before _ request state.edges⟩

/-- Node completion cannot create a running request in either memo family. -/
theorem finishNode_running_before (handle : Nat) (value : Value Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains (SourceRecursiveIntersectionThunks.finishNode handle value state) state :=
  ⟨FlatMemoThunk.finish_running_before handle value state.nodes, FlatMemoThunk.Running.refl _⟩

/-- Edge completion cannot create a running request in either memo family. -/
theorem finishEdge_running_before (handle : Nat) (value : EdgeValue Symbol Guard) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Retains (SourceRecursiveIntersectionThunks.finishEdge handle value state) state :=
  ⟨FlatMemoThunk.Running.refl _, FlatMemoThunk.finish_running_before handle value state.edges⟩

/-- Node demand can create a running node only at its selected handle. -/
theorem demandNode_running_before_other (handle other : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (observation : FlatMemoThunk.Observation (NodeRequest Symbol Guard) (Value Symbol Guard))
    (demanded : demandNode handle state = (observation, after)) (request : NodeRequest Symbol Guard)
    (different : other ≠ handle) (running : after.nodes.cells other = some ⟨request, .evaluating⟩) :
    state.nodes.cells other = some ⟨request, .evaluating⟩ := by
  apply FlatMemoThunk.demand_running_before_other handle other state.nodes request different
  have same : (FlatMemoThunk.demand handle state.nodes).2 = after.nodes := congrArg (fun actual => actual.2.nodes) demanded
  rw [same]
  exact running

/-- Edge demand can create a running edge only at its selected handle. -/
theorem demandEdge_running_before_other (handle other : Nat) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (observation : FlatMemoThunk.Observation (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (demanded : demandEdge handle state = (observation, after)) (request : EdgeRequest Symbol Guard)
    (different : other ≠ handle) (running : after.edges.cells other = some ⟨request, .evaluating⟩) :
    state.edges.cells other = some ⟨request, .evaluating⟩ := by
  apply FlatMemoThunk.demand_running_before_other handle other state.edges request different
  have same : (FlatMemoThunk.demand handle state.edges).2 = after.edges := congrArg (fun actual => actual.2.edges) demanded
  rw [same]
  exact running

/-- A completed source body leaves only the requests that were already running before it. -/
theorem Evaluation.running_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) :
    BodyCode code → Shape state → Retains after state := by
  induction evaluated with
  | pure => intro clean shape; exact Retains.refl _
  | work tail ih | enter tail ih | read tail ih | optionalBinder done tail ih =>
      intro clean shape
      exact ih (clean _) shape
  | @nodeDirect A request actual next state chosen middle final value result lookup body tail bodyIH tailIH =>
      intro clean shape
      have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
      have built := body.retains (compileNode_bodyCode actual) chosenShape
      exact (tailIH (clean value) built.1).trans
        ((bodyIH (compileNode_bodyCode actual) chosenShape).trans (by simpa only [lookup] using lookupNode_running_before request state))
  | @nodeReady A request next state chosen current final handle value result lookup demand tail ih =>
      intro clean shape
      have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
      have unchanged := (demandNode_ready handle chosen current value demand).choose_spec.2
      subst current
      exact (ih (clean value) chosenShape).trans (by simpa only [lookup] using lookupNode_running_before request state)
  | @edgeReady A request next state chosen current final handle value result lookup demand tail ih =>
      intro clean shape
      have chosenShape : Shape chosen := by simpa only [lookup] using lookupEdge_shape request state shape
      have unchanged := (demandEdge_ready handle chosen current value demand).choose_spec.2
      subst current
      exact (ih (clean value) chosenShape).trans (by simpa only [lookup] using lookupEdge_running_before request state)
  | @nodeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
      intro clean shape
      have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
      have currentShape : Shape current := by simpa only [demand] using demandNode_shape handle chosen chosenShape
      have built := body.retains (compileNode_bodyCode actual) currentShape
      have bodyBefore := bodyIH (compileNode_bodyCode actual) currentShape
      have tailBefore := tailIH (clean value) (finishNode_shape handle value middle built.1)
      have published : Retains chosen state := by simpa only [lookup] using lookupNode_running_before request state
      constructor
      · intro other original running
        have afterFinish := tailBefore.1 other original running
        have different : other ≠ handle := by
          intro same
          subst other
          exact FlatMemoThunk.finish_not_running handle value middle.nodes original afterFinish
        have beforeFinish := (finishNode_running_before handle value middle).1 other original afterFinish
        have beforeBody := bodyBefore.1 other original beforeFinish
        exact published.1 other original (demandNode_running_before_other handle other chosen current _ demand original different beforeBody)
      · intro other original running
        have beforeBody := bodyBefore.2 other original (tailBefore.2 other original running)
        have same : chosen.edges = current.edges := congrArg (fun actual => actual.2.edges) demand
        rw [← same] at beforeBody
        exact published.2 other original beforeBody
  | @edgeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
      intro clean shape
      have chosenShape : Shape chosen := by simpa only [lookup] using lookupEdge_shape request state shape
      have currentShape : Shape current := by simpa only [demand] using demandEdge_shape handle chosen chosenShape
      have built := body.retains (compileEdge_bodyCode emptyGuard conjoin actual) currentShape
      have bodyBefore := bodyIH (compileEdge_bodyCode emptyGuard conjoin actual) currentShape
      have tailBefore := tailIH (clean value) (finishEdge_shape handle value middle built.1)
      have published : Retains chosen state := by simpa only [lookup] using lookupEdge_running_before request state
      constructor
      · intro other original running
        have beforeBody := bodyBefore.1 other original (tailBefore.1 other original running)
        have same : chosen.nodes = current.nodes := congrArg (fun actual => actual.2.nodes) demand
        rw [← same] at beforeBody
        exact published.1 other original beforeBody
      · intro other original running
        have afterFinish := tailBefore.2 other original running
        have different : other ≠ handle := by
          intro same
          subst other
          exact FlatMemoThunk.finish_not_running handle value middle.edges original afterFinish
        have beforeFinish := (finishEdge_running_before handle value middle).2 other original afterFinish
        have beforeBody := bodyBefore.2 other original beforeFinish
        exact published.2 other original (demandEdge_running_before_other handle other chosen current _ demand original different beforeBody)
  | finishNode | finishEdge => intro clean; contradiction

/-- Actual completed native source code leaves no newly running memo request. -/
theorem done_running_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (done : execute emptyGuard conjoin fuel code state = .done value after) (clean : BodyCode code) (shape : Shape state) :
    Retains after state :=
  (evaluation_of_done emptyGuard conjoin fuel code state after value done).running_before clean shape

/-- A completed node body and its original finish restore the running cells from before demand. -/
theorem node_body_finish_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : NodeRequest Symbol Guard) (chosen current middle : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : Value Symbol Guard) (demand : demandNode handle chosen = (.evaluate request, current)) (shape : Shape current)
    (body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode request) current value middle) :
    Retains (SourceRecursiveIntersectionThunks.finishNode handle value middle) chosen := by
  have before := body.running_before (compileNode_bodyCode request) shape
  constructor
  · intro other original running
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle value middle.nodes original running
    have atBody := (finishNode_running_before handle value middle).1 other original running
    exact demandNode_running_before_other handle other chosen current _ demand original different (before.1 other original atBody)
  · intro other original running
    have atBody := before.2 other original running
    have same : chosen.edges = current.edges := congrArg (fun actual => actual.2.edges) demand
    rw [← same] at atBody
    exact atBody

/-- A completed edge body and its original finish restore the running cells from before demand. -/
theorem edge_body_finish_before [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (chosen current middle : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : EdgeValue Symbol Guard) (demand : demandEdge handle chosen = (.evaluate request, current)) (shape : Shape current)
    (body : Evaluation width Symbol Guard emptyGuard conjoin (compileEdge emptyGuard conjoin request) current value middle) :
    Retains (SourceRecursiveIntersectionThunks.finishEdge handle value middle) chosen := by
  have before := body.running_before (compileEdge_bodyCode emptyGuard conjoin request) shape
  constructor
  · intro other original running
    have atBody := before.1 other original running
    have same : chosen.nodes = current.nodes := congrArg (fun actual => actual.2.nodes) demand
    rw [← same] at atBody
    exact atBody
  · intro other original running
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle value middle.edges original running
    have atBody := (finishEdge_running_before handle value middle).2 other original running
    exact demandEdge_running_before_other handle other chosen current _ demand original different (before.2 other original atBody)

end MicroCFTA.SourceRecursiveIntersectionNative
