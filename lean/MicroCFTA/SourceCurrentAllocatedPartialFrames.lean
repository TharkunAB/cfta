import MicroCFTA.SourceCurrentAllocatedPartialGraph

/-!
# Structural frames for both current caller result families

Completed graph calls retain every earlier evaluating and returned cell.
Only their own newly started cell can change from evaluating to returned.
The proof uses the actual mutual graph and the literal thunk protocol.
It requires no input language, body result law, or recursive completion law.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialFrames
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo

/-- Pure key links and cell bounds do not depend on the changing equality cache. -/
structure Protocol (state : Caller width) : Prop where
  nodes : FlatMemoThunk.Valid (fun request key => request.key = key) (fun _ => True) state.nodeResults
  edges : FlatMemoThunk.Valid (fun request key => request.key = key) (fun _ => True) state.edgeResults

/-- The stronger current-cache structural invariant supplies the pure protocol. -/
theorem Protocol.of_valid {state : Caller width} (valid : SourceCurrentAllocatedPartialState.Valid state) : Protocol state :=
  ⟨FlatMemoThunk.Valid.keyMap _ _ _ _ valid.nodes (fun _ _ linked => linked.2),
    FlatMemoThunk.Valid.keyMap _ _ _ _ valid.edges (fun _ _ linked => linked.2)⟩

/-- Cold result families derive their protocol without input or body facts. -/
theorem initial_protocol (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) :
    Protocol (initial checked merge fourth) := Protocol.of_valid (initial_valid checked merge fourth)

/-- Each family retains its published handles, protected requests, and completed results. -/
structure Frame (before after : Caller width) : Prop where
  valid : Protocol after
  node_keys : Cache.Extends before.nodeResults.table after.nodeResults.table
  edge_keys : Cache.Extends before.edgeResults.table after.edgeResults.table
  node_running : FlatMemoThunk.Running before.nodeResults after.nodeResults
  edge_running : FlatMemoThunk.Running before.edgeResults after.edgeResults
  node_returned : FlatMemoThunk.Returned before.nodeResults after.nodeResults
  edge_returned : FlatMemoThunk.Returned before.edgeResults after.edgeResults

/-- An unchanged caller retains every protected cell. -/
theorem Frame.refl (state : Caller width) (valid : Protocol state) : Frame state state :=
  ⟨valid, Cache.extends_refl _, Cache.extends_refl _, .refl _, .refl _, .refl _, .refl _⟩

/-- Consecutive actual frames retain the original protected cells in both families. -/
theorem Frame.trans {before middle after : Caller width} (first : Frame before middle) (second : Frame middle after) :
    Frame before after :=
  ⟨second.valid, Cache.extends_trans first.node_keys second.node_keys, Cache.extends_trans first.edge_keys second.edge_keys,
    first.node_running.trans second.node_running, first.edge_running.trans second.edge_running,
    first.node_returned.trans second.node_returned, first.edge_returned.trans second.edge_returned⟩

/-- Checked heap and operation work retains both complete caller result tables. -/
theorem advance_frame (before : Caller width) (checked : Checked width) (fourth : Fourth) (merge : MergeMemo)
    (valid : Protocol before) : Frame before (advance before checked fourth merge) :=
  ⟨⟨valid.nodes, valid.edges⟩, Cache.extends_refl _, Cache.extends_refl _, .refl _, .refl _, .refl _, .refl _⟩

private theorem demand_table (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand, found, phase, FlatMemoThunk.setStatus]

private theorem finish_table (handle : Nat) (result : Result) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.finish handle result memo).table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.finish, found]
  | some cell => cases cell with
    | mk request status => cases status <;> simp only [FlatMemoThunk.finish, found, FlatMemoThunk.setStatus]

/-- Actual node publication and demand preserve protected cells in both families. -/
theorem beginNode_frame (request : NodeRequest) (before : Caller width) (valid : Protocol before) :
    Frame before (beginNode request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have linked := FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ valid.nodes rfl trivial
  refine ⟨⟨FlatMemoThunk.demand_valid published.1 published.2 _ linked, valid.edges⟩, ?_, Cache.extends_refl _,
    (FlatMemoThunk.lookup_running _ _ _ _ valid.nodes).trans (FlatMemoThunk.demand_running published.1 published.2),
    .refl _, (FlatMemoThunk.lookup_returned _ _ _ _ valid.nodes).trans
      (FlatMemoThunk.demand_returned published.1 published.2), .refl _⟩
  change Cache.Extends _ (FlatMemoThunk.demand published.1 published.2).2.table
  rw [demand_table]
  exact FlatMemoThunk.lookup_extends request.key request before.nodeResults

/-- Actual edge publication and demand preserve the independent node family as well. -/
theorem beginEdge_frame (request : EdgeRequest) (before : Caller width) (valid : Protocol before) :
    Frame before (beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have linked := FlatMemoThunk.lookup_valid request.key request before.edgeResults _ _ valid.edges rfl trivial
  refine ⟨⟨valid.nodes, FlatMemoThunk.demand_valid published.1 published.2 _ linked⟩, Cache.extends_refl _, ?_,
    .refl _, (FlatMemoThunk.lookup_running _ _ _ _ valid.edges).trans (FlatMemoThunk.demand_running published.1 published.2),
    .refl _, (FlatMemoThunk.lookup_returned _ _ _ _ valid.edges).trans
      (FlatMemoThunk.demand_returned published.1 published.2)⟩
  change Cache.Extends _ (FlatMemoThunk.demand published.1 published.2).2.table
  rw [demand_table]
  exact FlatMemoThunk.lookup_extends request.key request before.edgeResults

/-- An actual node start retains its exact owner and the candidate's published key. -/
theorem beginNode_owner (request : NodeRequest) (before : Caller width) (handle : Nat)
    (original : NodeRequest) (running : Caller width) (valid : Protocol before)
    (started : beginNode request before = (handle, .evaluate original, running)) :
    running.nodeResults.cells handle = some ⟨original, .evaluating⟩ ∧ original.key = request.key := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => result.2.1) started
  have found := FlatMemoThunk.demand_evaluate published.1 published.2
    (FlatMemoThunk.demand published.1 published.2).2 original (Prod.ext observed rfl)
  have present : (beginNode request before).2.2.nodeResults.cells (beginNode request before).1 =
      some ⟨original, .evaluating⟩ := found.2
  have stored : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  have protocol := (beginNode_frame request before valid).valid
  rw [started] at present stored protocol
  obtain ⟨cell, cellStored, linked⟩ := protocol.nodes.linked request.key handle stored
  have same := Option.some.inj (cellStored.symm.trans present)
  subst cell
  exact ⟨present, linked⟩

/-- An actual edge start retains its own exact owner in the separate result family. -/
theorem beginEdge_owner (request : EdgeRequest) (before : Caller width) (handle : Nat)
    (original : EdgeRequest) (running : Caller width) (valid : Protocol before)
    (started : beginEdge request before = (handle, .evaluate original, running)) :
    running.edgeResults.cells handle = some ⟨original, .evaluating⟩ ∧ original.key = request.key := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have observed := congrArg (fun result => result.2.1) started
  have found := FlatMemoThunk.demand_evaluate published.1 published.2
    (FlatMemoThunk.demand published.1 published.2).2 original (Prod.ext observed rfl)
  have present : (beginEdge request before).2.2.edgeResults.cells (beginEdge request before).1 =
      some ⟨original, .evaluating⟩ := found.2
  have stored : (beginEdge request before).2.2.edgeResults.table request.key = some (beginEdge request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  have protocol := (beginEdge_frame request before valid).valid
  rw [started] at present stored protocol
  obtain ⟨cell, cellStored, linked⟩ := protocol.edges.linked request.key handle stored
  have same := Option.some.inj (cellStored.symm.trans present)
  subst cell
  exact ⟨present, linked⟩

/-- Finishing this node preserves every protected input cell when its handle was not running there. -/
theorem finishNode_frame {before middle : Caller width} (handle : Nat) (result : Node) (frame : Frame before middle)
    (different : ∀ original, before.nodeResults.cells handle ≠ some ⟨original, .evaluating⟩) :
    Frame before (finishNode handle result middle) := by
  refine ⟨⟨FlatMemoThunk.finish_valid _ _ _ _ frame.valid.nodes, frame.valid.edges⟩, ?_, frame.edge_keys,
    ?_, frame.edge_running, frame.node_returned.trans (FlatMemoThunk.finish_returned _ _ _), frame.edge_returned⟩
  · simpa only [finishNode, finish_table] using frame.node_keys
  · intro other original stored
    have separate : other ≠ handle := by intro same; subst other; exact different original stored
    exact FlatMemoThunk.finish_running_other handle other result middle.nodeResults original separate
      (frame.node_running other original stored)

/-- Finishing this edge cannot change an ancestor's protected running or returned cell. -/
theorem finishEdge_frame {before middle : Caller width} (handle : Nat) (result : Edge) (frame : Frame before middle)
    (different : ∀ original, before.edgeResults.cells handle ≠ some ⟨original, .evaluating⟩) :
    Frame before (finishEdge handle result middle) := by
  refine ⟨⟨frame.valid.nodes, FlatMemoThunk.finish_valid _ _ _ _ frame.valid.edges⟩, frame.node_keys, ?_,
    frame.node_running, ?_, frame.node_returned, frame.edge_returned.trans (FlatMemoThunk.finish_returned _ _ _)⟩
  · simpa only [finishEdge, finish_table] using frame.edge_keys
  · intro other original stored
    have separate : other ≠ handle := by intro same; subst other; exact different original stored
    exact FlatMemoThunk.finish_running_other handle other result middle.edgeResults original separate
      (frame.edge_running other original stored)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem node_handle_not_running {budget : Nat} {request : NodeRequest} {before after : Caller width}
    {result : Node} {handle : Nat} (actual : NodeCall budget request before result after) (valid : Protocol before)
    (chosen : (beginNode request before).1 = handle) :
    ∀ original, before.nodeResults.cells handle ≠ some ⟨original, .evaluating⟩ := by
  intro original running
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have handles : published.1 = handle := chosen
  have retained := FlatMemoThunk.lookup_running request.key request before.nodeResults _ valid.nodes handle original running
  have busy := FlatMemoThunk.demand_busy handle published.2 original retained
  have blocked : beginNode request before = (handle, .busy, { before with nodeResults := published.2 }) := by
    change (published.1, (FlatMemoThunk.demand published.1 published.2).1,
      { before with nodeResults := (FlatMemoThunk.demand published.1 published.2).2 }) = _
    rw [handles, busy]
  exact actual.not_busy blocked

private theorem edge_handle_not_running {budget : Nat} {request : EdgeRequest} {before after : Caller width}
    {result : Edge} {handle : Nat} (actual : EdgeCall budget request before result after) (valid : Protocol before)
    (chosen : (beginEdge request before).1 = handle) :
    ∀ original, before.edgeResults.cells handle ≠ some ⟨original, .evaluating⟩ := by
  intro original running
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have handles : published.1 = handle := chosen
  have retained := FlatMemoThunk.lookup_running request.key request before.edgeResults _ valid.edges handle original running
  have busy := FlatMemoThunk.demand_busy handle published.2 original retained
  have blocked : beginEdge request before = (handle, .busy, { before with edgeResults := published.2 }) := by
    change (published.1, (FlatMemoThunk.demand published.1 published.2).1,
      { before with edgeResults := (FlatMemoThunk.demand published.1 published.2).2 }) = _
    rw [handles, busy]
  exact actual.not_busy blocked


-- All eight endpoints use the actual mutual recursor with the same structural motives.
local macro "frame_induction" recursor:ident actual:ident valid:ident : tactic => `(tactic|
  (revert $valid
   apply $recursor
     (motive_1 := fun _ before _ after _ => Protocol before → Frame before after)
     (motive_2 := fun _ before _ after _ => Protocol before → Frame before after)
     (motive_3 := fun _ before _ after _ => Protocol before → Frame before after)
     (motive_4 := fun _ before _ after _ => Protocol before → Frame before after)
     (motive_5 := fun _ _ before _ after _ => Protocol before → Frame before after)
     (motive_6 := fun _ _ before _ after _ => Protocol before → Frame before after)
     (motive_7 := fun _ _ before _ after _ => Protocol before → Frame before after)
     (motive_8 := fun _ _ _ before _ after _ => Protocol before → Frame before after)
     (t := $actual)
   · intro request before handle running result started initialValid
     have first := beginNode_frame request before initialValid
     simpa only [started] using first
   · intro request before handle running original result middle started body ih initialValid
     have first := beginNode_frame request before initialValid
     simp only [started] at first
     have rest := ih first.valid
     exact finishNode_frame _ _ (first.trans rest)
       (node_handle_not_running (.evaluate started body) initialValid (congrArg Prod.fst started))
   · intro inherited before initialValid
     exact Frame.refl before initialValid
   · intro inherited entry members depth free before initialValid
     exact Frame.refl before initialValid
   · intro entry body depth ordinary result heap inherited before actual initialValid
     exact advance_frame _ _ _ _ initialValid
   · intro inherited edges before results middle entry depth free actual ih initialValid
     have first := ih initialValid
     exact first.trans (advance_frame _ _ _ _ first.valid)
   · intro request before handle running result started initialValid
     have first := beginEdge_frame request before initialValid
     simpa only [started] using first
   · intro request before handle running original result middle started body ih initialValid
     have first := beginEdge_frame request before initialValid
     simp only [started] at first
     have rest := ih first.valid
     exact finishEdge_frame _ _ (first.trans rest)
       (edge_handle_not_running (.evaluate started body) initialValid (congrArg Prod.fst started))
   · intro loaded inherited result checked fourth merge edge before field actual initialValid
     exact advance_frame _ _ _ _ initialValid
   · intro inherited before initialValid
     exact Frame.refl before initialValid
   · intro inherited original before narrowed middle result afterChildren originals results after edge children rest ihEdge ihChildren ihRest initialValid
     have first := ihEdge initialValid
     have second := ihChildren first.valid
     exact (first.trans second).trans (ihRest second.valid)
   · intro inherited payload before edge results middle combined actual ih initialValid
     have first : Frame before (prefixState before edge inherited) := advance_frame _ _ _ _ initialValid
     have second := ih first.valid
     exact (first.trans second).trans (advance_frame _ _ _ _ second.valid)
   · intro values before initialValid
     exact Frame.refl before initialValid
   · intro identity records values before results after actual ih initialValid
     exact ih initialValid
   · intro combined index before initialValid
     exact Frame.refl before initialValid
   · intro before combined index value result middle values results after head rest ihHead ihRest initialValid
     have first : Frame before (descend before combined index).2 := advance_frame _ _ _ _ initialValid
     have second := ihHead first.valid
     exact (first.trans second).trans (ihRest second.valid)))

/-- Actual completed node calls retain both families' protected cells. -/
theorem node_call {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeCall budget request before result after) (valid : Protocol before) : Frame before after := by
  frame_induction NodeCall.rec actual valid

/-- Source node bodies preserve protected cells through their actual ordered row graph. -/
theorem node_body {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeBody budget request before result after) (valid : Protocol before) : Frame before after := by
  frame_induction NodeBody.rec actual valid

/-- Actual completed edge calls retain both protected result families. -/
theorem edge_call {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) (valid : Protocol before) : Frame before after := by
  frame_induction EdgeCall.rec actual valid

/-- The checked parent-edge body changes no caller result cell. -/
theorem edge_body {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeBody budget request before result after) (valid : Protocol before) : Frame before after := by
  frame_induction EdgeBody.rec actual valid

/-- Source row order threads the returned edge and descendant frames before the tail. -/
theorem rows {budget : Nat} {inherited : EqValue} {before after : Caller width} {values results : List Edge}
    (actual : Rows budget inherited values before results after) (valid : Protocol before) : Frame before after := by
  frame_induction Rows.rec actual valid

/-- The actual returned-edge prefix and raw reconstruction retain both caller tables. -/
theorem descendants {budget : Nat} {inherited : EqValue} {before after : Caller width} {value result : Edge}
    (actual : Descendants budget inherited value before result after) (valid : Protocol before) : Frame before after := by
  frame_induction Descendants.rec actual valid

/-- Contradiction skips child calls; live children preserve both families through their actual walk. -/
theorem children {budget : Nat} {combined : EqValue} {before after : Caller width} {values results : List Node}
    (actual : Children budget combined values before results after) (valid : Protocol before) : Frame before after := by
  frame_induction Children.rec actual valid

/-- Each actual descent and recursive node return preserves protected cells before the next index. -/
theorem walk {budget : Nat} {combined : EqValue} {index : Nat} {before after : Caller width} {values results : List Node}
    (actual : Walk budget combined index values before results after) (valid : Protocol before) : Frame before after := by
  frame_induction Walk.rec actual valid

end MicroCFTA.SourceCurrentAllocatedPartialFrames
