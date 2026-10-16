import MicroCFTA.SourceCurrentAllocatedPartialActiveOrder

/-!
# Active owners after completed current caller graphs

Every evaluating cell after a completed call was evaluating before it.
The proof follows all eight current graph families and both thunk tables.
It retains arbitrary ancestor bounds and excluded owner handles.
This preserves a progress invariant after completed recursive prefixes.
It does not supply a future completion graph or prove general termination.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialActiveOrder (ActiveExcept ActiveAbove)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- Both completed result families leave no new evaluating owner. -/
structure NoNewActive (before after : Caller width) : Prop where
  nodes : FlatMemoThunk.Running after.nodeResults before.nodeResults
  edges : FlatMemoThunk.Running after.edgeResults before.edgeResults

/-- An unchanged caller has the same evaluating owners. -/
theorem NoNewActive.refl (state : Caller width) : NoNewActive state state :=
  ⟨.refl _, .refl _⟩

/-- Consecutive completed prefixes leave no new evaluating owner. -/
theorem NoNewActive.trans {before middle after : Caller width}
    (first : NoNewActive before middle) (last : NoNewActive middle after) : NoNewActive before after :=
  ⟨last.nodes.trans first.nodes, last.edges.trans first.edges⟩

/-- Lower checked work changes neither outer result family. -/
theorem advance (before : Caller width) (checked : SourceEqualityNativeDemand.State width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    NoNewActive before (SourceCurrentAllocatedPartialState.advance before checked fourth merge) :=
  ⟨.refl _, .refl _⟩

/-- Every ancestor bound and excluded owner handle survives a completed prefix. -/
theorem NoNewActive.activeExcept {before after : Caller width} (frame : NoNewActive before after)
    {bound : Nat} {nodeSkip edgeSkip : Option Nat} (active : ActiveExcept bound nodeSkip edgeSkip before) :
    ActiveExcept bound nodeSkip edgeSkip after :=
  ⟨fun handle owner different found => active.nodes handle owner different (frame.nodes handle owner found),
    fun handle owner different found => active.edges handle owner different (frame.edges handle owner found)⟩

private theorem ready_running (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) (value : Result)
    (ready : (FlatMemoThunk.demand handle memo).1 = .ready value) :
    FlatMemoThunk.Running (FlatMemoThunk.demand handle memo).2 memo := by
  obtain ⟨_, _, same⟩ := FlatMemoThunk.demand_ready_original handle memo value _ (Prod.ext ready rfl)
  exact fun other _ found => (congrArg (fun state => state.cells other) same).symm.trans found

variable {width : Nat}

private theorem node_other (request : NodeRequest) (before : Caller width) (other : Nat) (owner : NodeRequest)
    (different : other ≠ (beginNode request before).1)
    (found : (beginNode request before).2.2.nodeResults.cells other = some ⟨owner, .evaluating⟩) :
    before.nodeResults.cells other = some ⟨owner, .evaluating⟩ :=
  FlatMemoThunk.lookup_running_before request.key request before.nodeResults other owner
    (FlatMemoThunk.demand_running_before_other _ other _ owner different found)

private theorem edge_other (request : EdgeRequest) (before : Caller width) (other : Nat) (owner : EdgeRequest)
    (different : other ≠ (beginEdge request before).1)
    (found : (beginEdge request before).2.2.edgeResults.cells other = some ⟨owner, .evaluating⟩) :
    before.edgeResults.cells other = some ⟨owner, .evaluating⟩ :=
  FlatMemoThunk.lookup_running_before request.key request before.edgeResults other owner
    (FlatMemoThunk.demand_running_before_other _ other _ owner different found)

private theorem node_hit {request : NodeRequest} {before running : Caller width} {handle : Nat} {result : Node}
    (started : beginNode request before = (handle, .ready result, running)) : NoNewActive before running := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have ready : (FlatMemoThunk.demand published.1 published.2).1 = .ready result :=
    congrArg (fun actual => actual.2.1) started
  have nodes := (ready_running published.1 published.2 result ready).trans
    (FlatMemoThunk.lookup_running_before request.key request before.nodeResults)
  change FlatMemoThunk.Running (beginNode request before).2.2.nodeResults before.nodeResults at nodes
  have components := beginNode_components request before
  rw [started] at nodes components
  dsimp only at components
  exact ⟨nodes, by simpa only [components.2.2.2] using FlatMemoThunk.Running.refl before.edgeResults⟩

private theorem edge_hit {request : EdgeRequest} {before running : Caller width} {handle : Nat} {result : Edge}
    (started : beginEdge request before = (handle, .ready result, running)) : NoNewActive before running := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have ready : (FlatMemoThunk.demand published.1 published.2).1 = .ready result :=
    congrArg (fun actual => actual.2.1) started
  have edges := (ready_running published.1 published.2 result ready).trans
    (FlatMemoThunk.lookup_running_before request.key request before.edgeResults)
  change FlatMemoThunk.Running (beginEdge request before).2.2.edgeResults before.edgeResults at edges
  have components := beginEdge_components request before
  rw [started] at edges components
  dsimp only at components
  exact ⟨by simpa only [components.2.2.2] using FlatMemoThunk.Running.refl before.nodeResults, edges⟩

private theorem node_evaluate {request owner : NodeRequest} {before running middle : Caller width}
    {handle : Nat} (result : Node)
    (started : beginNode request before = (handle, .evaluate owner, running))
    (body : NoNewActive running middle) : NoNewActive before (finishNode handle result middle) := by
  have components := beginNode_components request before
  rw [started] at components
  dsimp only at components
  constructor
  · intro other original found
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle result middle.nodeResults original found
    have earlier := body.nodes other original
      (FlatMemoThunk.finish_running_before handle result middle.nodeResults other original found)
    exact node_other request before other original (by simpa only [started] using different)
      (by simpa only [started] using earlier)
  · intro other original found
    simpa only [components.2.2.2] using body.edges other original found

private theorem edge_evaluate {request owner : EdgeRequest} {before running middle : Caller width}
    {handle : Nat} (result : Edge)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (body : NoNewActive running middle) : NoNewActive before (finishEdge handle result middle) := by
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  constructor
  · intro other original found
    simpa only [components.2.2.2] using body.nodes other original found
  · intro other original found
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle result middle.edgeResults original found
    have earlier := body.edges other original
      (FlatMemoThunk.finish_running_before handle result middle.edgeResults other original found)
    exact edge_other request before other original (by simpa only [started] using different)
      (by simpa only [started] using earlier)

local macro "active_induction" recursor:ident actual:ident : tactic => `(tactic|
  (apply $recursor
     (motive_1 := fun _ before _ after _ => NoNewActive before after)
     (motive_2 := fun _ before _ after _ => NoNewActive before after)
     (motive_3 := fun _ before _ after _ => NoNewActive before after)
     (motive_4 := fun _ before _ after _ => NoNewActive before after)
     (motive_5 := fun _ _ before _ after _ => NoNewActive before after)
     (motive_6 := fun _ _ before _ after _ => NoNewActive before after)
     (motive_7 := fun _ _ before _ after _ => NoNewActive before after)
     (motive_8 := fun _ _ _ before _ after _ => NoNewActive before after)
     (t := $actual)
   · intro request before handle running result started
     exact node_hit started
   · intro request before handle running original result middle started body ih
     exact node_evaluate result started ih
   · intro inherited before
     exact NoNewActive.refl before
   · intro inherited entry members depth free before
     exact NoNewActive.refl before
   · intro entry body depth ordinary result heap inherited before actual
     exact advance _ _ _ _
   · intro inherited edges before results middle entry depth free actual ih
     exact ih.trans (advance _ _ _ _)
   · intro request before handle running result started
     exact edge_hit started
   · intro request before handle running original result middle started body ih
     exact edge_evaluate result started ih
   · intro loaded inherited result checked fourth merge edge before field actual
     exact advance _ _ _ _
   · intro inherited before
     exact NoNewActive.refl before
   · intro inherited original before narrowed middle result afterChildren originals results after edge children rest ihEdge ihChildren ihRest
     exact (ihEdge.trans ihChildren).trans ihRest
   · intro inherited payload before edge results middle combined actual ih
     exact ((advance before _ _ _).trans ih).trans (advance _ _ _ _)
   · intro values before
     exact NoNewActive.refl before
   · intro identity records values before results after actual ih
     exact ih
   · intro combined index before
     exact NoNewActive.refl before
   · intro before combined index value result middle values results after head rest ihHead ihRest
     exact ((advance before _ _ _).trans ihHead).trans ihRest))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A completed node call leaves no new active owner in either family. -/
theorem node_call {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeCall budget request before result after) : NoNewActive before after := by
  active_induction NodeCall.rec actual

/-- A completed node body retains the active ancestors of its actual row prefixes. -/
theorem node_body {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeBody budget request before result after) : NoNewActive before after := by
  active_induction NodeBody.rec actual

/-- A completed edge call removes its own evaluating phase and leaves no new owner. -/
theorem edge_call {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) : NoNewActive before after := by
  active_induction EdgeCall.rec actual

/-- A completed parent body retains the exact outer result tables. -/
theorem edge_body {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeBody budget request before result after) : NoNewActive before after := by
  active_induction EdgeBody.rec actual

/-- Ordered row prefixes and returned-edge descendants leave no new active owner. -/
theorem rows {budget : Nat} {inherited : EqValue} {before after : Caller width} {values results : List Edge}
    (actual : Rows budget inherited values before results after) : NoNewActive before after := by
  active_induction Rows.rec actual

/-- The actual inherited prefix and raw rebuilding preserve ancestor order. -/
theorem descendants {budget : Nat} {inherited : EqValue} {before after : Caller width} {value result : Edge}
    (actual : Descendants budget inherited value before result after) : NoNewActive before after := by
  active_induction Descendants.rec actual

/-- Contradiction and live child walks both leave no new active owner. -/
theorem children {budget : Nat} {combined : EqValue} {before after : Caller width} {values results : List Node}
    (actual : Children budget combined values before results after) : NoNewActive before after := by
  active_induction Children.rec actual

/-- Indexed child calls retain the ancestor bound before the next literal child. -/
theorem walk {budget : Nat} {combined : EqValue} {index : Nat} {before after : Caller width} {values results : List Node}
    (actual : Walk budget combined index values before results after) : NoNewActive before after := by
  active_induction Walk.rec actual

end MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
