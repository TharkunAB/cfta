import MicroCFTA.SourceRecursiveIntersectionNativeShape

/-!
# Completed source bodies retain enclosing running requests

Induction over actual nested evaluations preserves memo structure and every
already-running enclosing request. A nested request can complete only its
own newly started cell. Concrete semantic completion provenance remains a
separate source correspondence obligation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Every completed source body retains both memo structures and all enclosing running cells. -/
theorem Evaluation.retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after) :
    BodyCode code → Shape state → Shape after ∧ Retains state after := by
  induction evaluated with
  | pure => intro clean shape; exact ⟨shape, Retains.refl _⟩
  | work tail ih | enter tail ih | read tail ih | optionalBinder done tail ih =>
    intro clean shape
    exact ih (clean _) shape
  | @nodeDirect A request actual next state chosen middle final value result lookup body tail bodyIH tailIH =>
    intro clean shape
    have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
    have entered : Retains state chosen := by simpa only [lookup] using lookupNode_retains request state shape
    have built := bodyIH (compileNode_bodyCode actual) chosenShape
    have finished := tailIH (clean value) built.1
    exact ⟨finished.1, entered.trans (built.2.trans finished.2)⟩
  | @nodeReady A request next state chosen current final handle value result lookup demand tail ih =>
    intro clean shape
    have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
    have currentShape : Shape current := by simpa only [demand] using demandNode_shape handle chosen chosenShape
    have published : Retains state chosen := by simpa only [lookup] using lookupNode_retains request state shape
    have demanded : Retains chosen current := by simpa only [demand] using demandNode_retains handle chosen
    have finished := ih (clean value) currentShape
    exact ⟨finished.1, published.trans (demanded.trans finished.2)⟩
  | @edgeReady A request next state chosen current final handle value result lookup demand tail ih =>
    intro clean shape
    have chosenShape : Shape chosen := by simpa only [lookup] using lookupEdge_shape request state shape
    have currentShape : Shape current := by simpa only [demand] using demandEdge_shape handle chosen chosenShape
    have published : Retains state chosen := by simpa only [lookup] using lookupEdge_retains request state shape
    have demanded : Retains chosen current := by simpa only [demand] using demandEdge_retains handle chosen
    have finished := ih (clean value) currentShape
    exact ⟨finished.1, published.trans (demanded.trans finished.2)⟩
  | @nodeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
    intro clean shape
    have chosenShape : Shape chosen := by simpa only [lookup] using lookupNode_shape request state shape
    have currentShape : Shape current := by simpa only [demand] using demandNode_shape handle chosen chosenShape
    have published : Retains state chosen := by simpa only [lookup] using lookupNode_retains request state shape
    have demanded : Retains chosen current := by simpa only [demand] using demandNode_retains handle chosen
    have entered := published.trans demanded
    have built := bodyIH (compileNode_bodyCode actual) currentShape
    have finished := tailIH (clean value) (finishNode_shape handle value middle built.1)
    refine ⟨finished.1, ?_, ?_⟩
    · intro other original running
      have beforeDemand := published.1 other original running
      have suspended := (demandNode_evaluate handle chosen current actual demand).1
      have different : other ≠ handle := by
        intro same
        subst other
        have impossible := Option.some.inj (beforeDemand.symm.trans suspended)
        cases impossible
      have inBody := built.2.1 other original (entered.1 other original running)
      exact finished.2.1 other original (FlatMemoThunk.finish_running_other handle other value middle.nodes original different inBody)
    · intro other original running
      exact finished.2.2 other original (built.2.2 other original (entered.2 other original running))
  | @edgeStarted A request actual next state chosen current middle final handle value result lookup demand body tail bodyIH tailIH =>
    intro clean shape
    have chosenShape : Shape chosen := by simpa only [lookup] using lookupEdge_shape request state shape
    have currentShape : Shape current := by simpa only [demand] using demandEdge_shape handle chosen chosenShape
    have published : Retains state chosen := by simpa only [lookup] using lookupEdge_retains request state shape
    have demanded : Retains chosen current := by simpa only [demand] using demandEdge_retains handle chosen
    have entered := published.trans demanded
    have built := bodyIH (compileEdge_bodyCode emptyGuard conjoin actual) currentShape
    have finished := tailIH (clean value) (finishEdge_shape handle value middle built.1)
    refine ⟨finished.1, ?_, ?_⟩
    · intro other original running
      exact finished.2.1 other original (built.2.1 other original (entered.1 other original running))
    · intro other original running
      have beforeDemand := published.2 other original running
      have suspended := (demandEdge_evaluate handle chosen current actual demand).1
      have different : other ≠ handle := by
        intro same
        subst other
        have impossible := Option.some.inj (beforeDemand.symm.trans suspended)
        cases impossible
      have inBody := built.2.2 other original (entered.2 other original running)
      exact finished.2.2 other original (FlatMemoThunk.finish_running_other handle other value middle.edges original different inBody)
  | finishNode | finishEdge => intro clean; cases clean

/-- Actual completed native source code preserves memo structure and every original running request. -/
theorem done_retains [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (done : execute emptyGuard conjoin fuel code state = .done value after) (clean : BodyCode code) (shape : Shape state) :
    Shape after ∧ Retains state after :=
  (evaluation_of_done emptyGuard conjoin fuel code state after value done).retains clean shape

/-- A completed compiled node body leaves its original running cell for the original completion frame. -/
theorem node_body_cell [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : NodeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : Value Symbol Guard) (shape : Shape state) (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin (compileNode request) state value after) :
    after.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value after).nodes.cells handle = some ⟨request, .returned value⟩ := by
  have retained := evaluated.retains (compileNode_bodyCode request) shape
  have present := retained.2.1 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.nodes request present⟩

/-- A completed compiled edge body leaves its original running cell for the original completion frame. -/
theorem edge_body_cell [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : EdgeValue Symbol Guard) (shape : Shape state) (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (evaluated : Evaluation width Symbol Guard emptyGuard conjoin (compileEdge emptyGuard conjoin request) state value after) :
    after.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishEdge handle value after).edges.cells handle = some ⟨request, .returned value⟩ := by
  have retained := evaluated.retains (compileEdge_bodyCode emptyGuard conjoin request) shape
  have present := retained.2.2 handle request running
  exact ⟨present, FlatMemoThunk.finish_evaluating handle value after.edges request present⟩

end MicroCFTA.SourceRecursiveIntersectionNative
