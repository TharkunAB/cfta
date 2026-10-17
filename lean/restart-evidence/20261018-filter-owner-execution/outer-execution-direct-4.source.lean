import MicroCFTA.SourceCurrentOuterActiveAncestry

/-!
# Actual busy outer executions and their enclosing node activations

Completed earlier calls derive their node-table facts directly from the
literal bounded worker. No completed graph, range certificate, or desired
prefix is a producer input. A reported node-busy failure supplies its exact
dispatch and an enclosing key-equal activation. The theorem does not exclude
that collision or prove completion.
-/
namespace MicroCFTA.SourceCurrentOuterExecutionAncestry
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

/-- Node key links and cell bounds refer to the exact current node table. -/
def NodeValid (state : Caller width) : Prop :=
  FlatMemoThunk.Valid (fun request key => request.key = key) (fun _ => True) state.nodeResults

private structure Frame (before after : Caller width) : Prop where
  valid : NodeValid after
  forward : FlatMemoThunk.Running before.nodeResults after.nodeResults
  reverse : FlatMemoThunk.Running after.nodeResults before.nodeResults

private theorem frame_same {before after : Caller width} (valid : NodeValid before)
    (same : after.nodeResults = before.nodeResults) : Frame before after := by
  constructor
  · unfold NodeValid at valid ⊢
    rw [same]
    exact valid
  · intro handle owner found
    simpa only [same] using found
  · intro handle owner found
    simpa only [same] using found

private theorem frame_trans {before middle after : Caller width}
    (first : Frame before middle) (last : Frame middle after) : Frame before after :=
  ⟨last.valid, first.forward.trans last.forward, last.reverse.trans first.reverse⟩

private def Completed (before : Caller width) : Outcome A width → Prop
  | .done _ after => Frame before after
  | .failed .. => True

private theorem completed_bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (checked : Completed start first)
    (later : ∀ value middle, Frame start middle → Completed before (next value middle)) :
    Completed before (first.bind next) := by
  cases first with
  | done value middle => exact later value middle checked
  | failed => trivial

private theorem completed_after {before middle : Caller width} (first : Frame before middle)
    (last : Completed middle (actual : Outcome A width)) : Completed before actual := by
  cases actual with
  | done => exact frame_trans first last
  | failed => trivial

private theorem erase_failed {actual : Outcome A width}
    (failed : actual.bind (fun _ after => .done () after) = .failed fault after) :
    actual = .failed fault after := by
  cases actual <;> simp_all [Outcome.bind]

private theorem start_valid (request : NodeRequest) (before : Caller width) (valid : NodeValid before) :
    NodeValid (beginNode request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  exact FlatMemoThunk.demand_valid published.1 published.2 _
    (FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ valid rfl trivial)

private theorem start_forward (request : NodeRequest) (before : Caller width) (valid : NodeValid before) :
    FlatMemoThunk.Running before.nodeResults (beginNode request before).2.2.nodeResults :=
  (FlatMemoThunk.lookup_running _ _ _ _ valid).trans (FlatMemoThunk.demand_running _ _)

private theorem start_other (request : NodeRequest) (before : Caller width) (handle : Nat) (owner : NodeRequest)
    (different : handle ≠ (beginNode request before).1)
    (found : (beginNode request before).2.2.nodeResults.cells handle = some ⟨owner,.evaluating⟩) :
    before.nodeResults.cells handle = some ⟨owner,.evaluating⟩ :=
  FlatMemoThunk.lookup_running_before request.key request before.nodeResults handle owner
    (FlatMemoThunk.demand_running_before_other _ handle _ owner different found)

private theorem hit_frame (request : NodeRequest) (before : Caller width) (valid : NodeValid before)
    (started : beginNode request before = (handle,.ready result,running)) : Frame before running := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have actual : FlatMemoThunk.demand published.1 published.2 =
      (.ready result,(FlatMemoThunk.demand published.1 published.2).2) :=
    Prod.ext (congrArg (fun result => result.2.1) started) rfl
  obtain ⟨_,_,same⟩ := FlatMemoThunk.demand_ready_original published.1 published.2 result _ actual
  have reverse : FlatMemoThunk.Running (beginNode request before).2.2.nodeResults before.nodeResults := by
    intro other owner found
    exact FlatMemoThunk.lookup_running_before request.key request before.nodeResults other owner
      ((congrArg (fun state => state.cells other) same).symm.trans found)
  have checked := start_valid request before valid
  have forward := start_forward request before valid
  rw [started] at checked forward reverse
  exact ⟨checked,forward,reverse⟩

private theorem evaluate_frame (request : NodeRequest) (before : Caller width) (valid : NodeValid before)
    (started : beginNode request before = (handle,.evaluate original,running))
    (body : Frame running middle) (result : Node) : Frame before (finishNode handle result middle) := by
  have noOld : ∀ owner, before.nodeResults.cells handle ≠ some ⟨owner,.evaluating⟩ := by
    intro owner found
    let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
    have handles : published.1 = handle := congrArg Prod.fst started
    have old := FlatMemoThunk.lookup_running request.key request before.nodeResults _ valid handle owner found
    have busy := FlatMemoThunk.demand_busy handle published.2 owner old
    have observed : (FlatMemoThunk.demand published.1 published.2).1 = .evaluate original :=
      congrArg (fun actual => actual.2.1) started
    rw [handles,busy] at observed
    cases observed
  have first := start_forward request before valid
  rw [started] at first
  constructor
  · exact FlatMemoThunk.finish_valid _ _ _ _ body.valid
  · intro other owner found
    have different : other ≠ handle := by intro same; subst other; exact noOld owner found
    exact FlatMemoThunk.finish_running_other handle other result middle.nodeResults owner different
      (body.forward other owner (first other owner found))
  · intro other owner found
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle result middle.nodeResults owner found
    have earlier := body.reverse other owner (FlatMemoThunk.finish_running_before _ _ _ other owner found)
    exact start_other request before other owner (by simpa only [started] using different)
      (by simpa only [started] using earlier)

private theorem demand_table (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle memo).2.table = memo.table := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand,found,phase,FlatMemoThunk.setStatus]

private theorem start_owner (request : NodeRequest) (before : Caller width) (valid : NodeValid before)
    (started : beginNode request before = (handle,.evaluate owner,running)) :
    running.nodeResults.cells handle = some ⟨owner,.evaluating⟩ ∧ owner.key = request.key := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => result.2.1) started
  have evaluated := FlatMemoThunk.demand_evaluate published.1 published.2 _ owner (Prod.ext observed rfl)
  have present : (beginNode request before).2.2.nodeResults.cells (beginNode request before).1 =
      some ⟨owner,.evaluating⟩ := evaluated.2
  have linked : (beginNode request before).2.2.nodeResults.table request.key = some (beginNode request before).1 := by
    change (FlatMemoThunk.demand _ _).2.table _ = _
    rw [demand_table]
    exact FlatMemoThunk.lookup_stored _ _ _
  have final := start_valid request before valid
  rw [started] at present linked final
  obtain ⟨cell,found,key⟩ := final.linked request.key handle linked
  have same := Option.some.inj (found.symm.trans present)
  subst cell
  exact ⟨present,key⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private theorem edge_nodes (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width) :
    (edgeCall fuel g s r e p h m c n budget request before).state.nodeResults = before.nodeResults := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have same := (beginEdge_components request before).2.2.2
  rw [started] at same
  cases action <;> simp only [edgeCall,started]
  · exact same
  · unfold edgeBody
    split <;> exact same
  · exact same
  · exact same

private theorem edge_no_busy (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (failed : edgeCall fuel g s r e p h m c n budget request before = .failed (.nodeMemo handle .busy) after) : False := by
  rcases started : beginEdge request before with ⟨chosen,action,running⟩
  cases action <;> simp only [edgeCall,started] at failed
  · cases failed
  · unfold edgeBody at failed
    split at failed <;> cases failed
  · cases failed
  · cases failed

private theorem edge_frame (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (valid : NodeValid before) : Completed before (edgeCall fuel g s r e p h m c n budget request before) := by
  cases actual : edgeCall fuel g s r e p h m c n budget request before with
  | done result after =>
      have same := edge_nodes fuel g s r e p h m c n budget request before
      rw [actual] at same
      exact frame_same valid same
  | failed => trivial

private def NodeAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width),
  NodeValid before → Completed before (nodeCall fuel g s r e p h m c n budget request before)
private def BodyAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width),
  NodeValid before → Completed before (nodeBody fuel g s r e p h m c n budget request before)
private def RowsAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited values (before : Caller width),
  NodeValid before → Completed before (rows fuel g s r e p h m c n budget inherited values before)
private def DescendantsAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited value (before : Caller width),
  NodeValid before → Completed before (descendants fuel g s r e p h m c n budget inherited value before)
private def ChildrenAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined values (before : Caller width),
  NodeValid before → Completed before (children fuel g s r e p h m c n budget combined values before)
private def WalkAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined index values (before : Caller width),
  NodeValid before → Completed before (walk fuel g s r e p h m c n budget combined index values before)

private theorem all_frames (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget combined index values before valid
      cases values with
      | nil => simpa only [walk,Completed] using frame_same valid rfl
      | cons value rest =>
        cases fuel with
        | zero => simp only [walk,Completed]
        | succ fuel =>
          simp only [walk]
          have head := (ih fuel (Nat.lt_succ_self _)).1 g s r e p h m c n budget
            ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1,value⟩
            (SourceCurrentAllocatedPartialGraph.descend before combined index).2 valid
          apply completed_bind _ _ head
          intro result middle first
          have first : Frame before middle := ⟨first.valid,first.forward,first.reverse⟩
          have tail := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 g s r e p h m c n budget combined (index+1) rest middle first.valid
          apply completed_bind _ _ (completed_after first tail)
          intro results after last
          exact last
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget combined values before valid
      cases combined with
      | contradiction => simpa only [children,Completed] using frame_same valid rfl
      | live identity records => simpa only [children] using walkAt g s r e p h m c n budget (.live identity records) 0 values before valid
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before valid
      simp only [descendants]
      split
      · trivial
      · trivial
      · rename_i combined _
        apply completed_bind _ _ (childrenAt g s r e p h m c n budget combined value.children
          (SourceCurrentAllocatedPartialGraph.prefixState before value inherited) valid)
        intro results after first
        exact ⟨first.valid,first.forward,first.reverse⟩
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before valid
      cases values with
      | nil => simpa only [rows,Completed] using frame_same valid rfl
      | cons value rest =>
        cases fuel with
        | zero => simp only [rows,Completed]
        | succ fuel =>
          simp only [rows]
          apply completed_bind _ _ (edge_frame _ _ _ _ _ _ _ _ _ _ _ _ _ valid)
          intro narrowed middle edge
          have child := (ih fuel (Nat.lt_succ_self _)).2.2.2.1 g s r e p h m c n budget inherited narrowed middle edge.valid
          apply completed_bind _ _ (completed_after edge child)
          intro result after first
          have tail := (ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n budget inherited rest after first.valid
          apply completed_bind _ _ (completed_after first tail)
          intro results final last
          exact last
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before valid
      rcases request with ⟨inherited,value⟩
      cases value with
      | empty | union => simpa only [nodeBody,Completed] using frame_same valid rfl
      | reference => simp only [nodeBody,Completed]
      | mu entry body depth ordinary =>
        simp only [nodeBody]
        split
        · exact frame_same valid rfl
        · trivial
      | node entry original depth free =>
        cases fuel with
        | zero => simp only [nodeBody,Completed]
        | succ fuel =>
          simp only [nodeBody]
          apply completed_bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n budget inherited original before valid)
          intro result after first
          exact ⟨first.valid,first.forward,first.reverse⟩
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before valid
      rcases started : beginNode request before with ⟨handle,action,running⟩
      cases action with
      | ready result => simpa only [nodeCall,started,Completed] using hit_frame request before valid started
      | absent | busy => simp only [nodeCall,started,Completed]
      | evaluate original =>
        have checked := start_valid request before valid
        rw [started] at checked
        simp only [nodeCall,started]
        apply completed_bind _ _ (bodyAt g s r e p h m c n budget original running checked)
        intro result middle first
        exact evaluate_frame request before valid started first result
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem node_done (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (valid : NodeValid before) : Frame before after := by
  have frame := (all_frames fuel).1 g s r e p h m c n budget request before valid
  rw [actual] at frame
  exact frame

private theorem descendants_done (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (valid : NodeValid before) : Frame before after := by
  have frame := (all_frames fuel).2.2.2.1 g s r e p h m c n budget inherited value before valid
  rw [actual] at frame
  exact frame

private theorem edge_done (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (valid : NodeValid before) : Frame before after := by
  have frame := edge_frame fuel g s r e p h m c n budget request before valid
  rw [actual] at frame
  exact frame

/-- A prefix enters a literal branch or skips only completed earlier calls. -/
inductive Step (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- A node enters its exact stored owner after demand. -/
  | node_evaluate (actual : beginNode request before = (handle, .evaluate original, running)) :
      Step g s r e p h m c n budget (.node fuel request before) (.body fuel original running)
  /-- An ordinary body enters its original rows. -/
  | body_rows (actual : request.value = .node entry originals depth free) :
      Step g s r e p h m c n budget (.body (fuel + 1) request before)
        (.rows fuel request.inherited originals before)
  /-- A completed parent edge precedes its actual descendants. -/
  | rows_edge
      (actual : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.descendants fuel inherited narrowed middle)
  /-- The row suffix starts after the exact completed parent and descendants. -/
  | rows_tail
      (edge : edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
      (children : descendants fuel g s r e p h m c n budget inherited narrowed middle = .done result after) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.rows fuel inherited rest after)
  /-- The inherited prefix enters the exact returned children. -/
  | descendants_children {edge : Edge}
      (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
        before.checked.operations).1 = .ok (some combined)) :
      Step g s r e p h m c n budget (.descendants fuel inherited edge before)
        (.children fuel combined edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited))
  /-- A live combined payload enters its indexed walk. -/
  | children_walk (live : combined ≠ .contradiction) :
      Step g s r e p h m c n budget (.children fuel combined values before) (.walk fuel combined 0 values before)
  /-- The next node uses the actual indexed descent. -/
  | walk_head :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
          (SourceCurrentAllocatedPartialGraph.descend before combined index).2)
  /-- The next slot starts after the actual completed earlier node. -/
  | walk_tail
      (actual : nodeCall fuel g s r e p h m c n budget
        ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
        (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle) :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.walk fuel combined (index + 1) rest middle)

/-- A finite literal prefix retains every completed earlier-call witness. -/
inductive Reached (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- The entry phase is already reached. -/
  | refl (phase) : Reached g s r e p h m c n budget phase phase
  /-- An actual branch extends the preceding prefix. -/
  | snoc (earlier : Reached g s r e p h m c n budget first middle)
      (last : Step g s r e p h m c n budget middle final) :
      Reached g s r e p h m c n budget first final

/-- Consecutive actual prefixes form one prefix. -/
theorem Reached.trans (first : Reached g s r e p h m c n budget entryPhase middle)
    (last : Reached g s r e p h m c n budget middle final) :
    Reached g s r e p h m c n budget entryPhase final := by
  induction last with
  | refl => exact first
  | snoc earlier last ih => exact .snoc ih last

private theorem step_forward (actual : Step g s r e p h m c n budget first last)
    (valid : NodeValid (caller first)) :
    NodeValid (caller last) ∧ FlatMemoThunk.Running (caller first).nodeResults (caller last).nodeResults := by
  cases actual with
  | node_evaluate started =>
    rename_i request before handle running original fuel
    have checked := start_valid request before valid
    have forward := start_forward request before valid
    rw [started] at checked forward
    exact ⟨checked,forward⟩
  | body_rows => exact ⟨valid,.refl _⟩
  | rows_edge done => exact ⟨(edge_done done valid).valid,(edge_done done valid).forward⟩
  | rows_tail edge children =>
    have first := edge_done edge valid
    have last := descendants_done children first.valid
    exact ⟨last.valid,first.forward.trans last.forward⟩
  | descendants_children => exact ⟨valid,.refl _⟩
  | children_walk => exact ⟨valid,.refl _⟩
  | walk_head => exact ⟨valid,.refl _⟩
  | walk_tail done =>
    have frame := node_done done valid
    exact ⟨frame.valid,frame.forward⟩

/-- Every actual prefix derives the validity of its reached node table. -/
theorem Reached.valid (actual : Reached g s r e p h m c n budget first last)
    (valid : NodeValid (caller first)) : NodeValid (caller last) := by
  induction actual with
  | refl => exact valid
  | snoc earlier last ih => exact (step_forward last ih).1

/-- An enclosing node owner remains exact throughout its unfinished prefix. -/
theorem Reached.running (actual : Reached g s r e p h m c n budget first last)
    (valid : NodeValid (caller first)) (handle : Nat) (owner : NodeRequest)
    (present : (caller first).nodeResults.cells handle = some ⟨owner,.evaluating⟩) :
    (caller last).nodeResults.cells handle = some ⟨owner,.evaluating⟩ := by
  induction actual with
  | refl => exact present
  | snoc earlier last ih => exact (step_forward last (earlier.valid valid)).2 handle owner ih

private theorem step_owner (step : Step g s r e p h m c n budget first last)
    (valid : NodeValid (caller first)) (handle : Nat) (owner : NodeRequest)
    (present : (caller last).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    (caller first).nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∨
      ∃ fuel request before running,
        first = .node fuel request before ∧ last = .body fuel owner running ∧
        beginNode request before = (handle, .evaluate owner, running) := by
  cases step with
  | node_evaluate actual =>
      rename_i request before chosen running original fuel
      by_cases same : handle = chosen
      · subst handle
        have own : running.nodeResults.cells chosen = some ⟨original, .evaluating⟩ :=
          (start_owner request before valid actual).1
        have equal : original = owner := by
          have cells := Option.some.inj (own.symm.trans present)
          exact congrArg FlatMemoThunk.Cell.request cells
        subst owner
        exact Or.inr ⟨fuel, request, before, running, rfl, rfl, actual⟩
      · apply Or.inl
        have earlier : (beginNode request before).2.2.nodeResults.cells handle = some ⟨owner, .evaluating⟩ := by
          rw [actual]
          exact present
        have chosenEq : (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 = chosen :=
          congrArg Prod.fst actual
        exact FlatMemoThunk.lookup_running_before request.key request before.nodeResults handle owner
          (FlatMemoThunk.demand_running_before_other _ handle _ owner (by rw [chosenEq]; exact same) earlier)
  | body_rows => exact Or.inl present
  | rows_edge done => exact Or.inl ((edge_done done valid).reverse _ _ present)
  | rows_tail edge children =>
      have first := edge_done edge valid
      exact Or.inl (first.reverse _ _ ((descendants_done children first.valid).reverse _ _ present))
  | descendants_children => exact Or.inl present
  | children_walk => exact Or.inl present
  | walk_head => exact Or.inl present
  | walk_tail done => exact Or.inl ((node_done done valid).reverse _ _ present)

/-- An ancestor retains its exact activation and an unfinished body-to-reader prefix. -/
def Ancestor (g s r e p h m c n budget : Nat) (entryPhase current : Phase width)
    (handle : Nat) (owner : NodeRequest) : Prop :=
  ∃ fuel request before running,
    Reached g s r e p h m c n budget entryPhase (.node fuel request before) ∧
    beginNode request before = (handle, .evaluate owner, running) ∧
    owner.key = request.key ∧ NodeValid running ∧
    running.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
    Reached g s r e p h m c n budget (.body fuel owner running) current

private theorem ancestor_extend (ancestor : Ancestor g s r e p h m c n budget entryPhase first handle owner)
    (step : Step g s r e p h m c n budget first last) :
    Ancestor g s r e p h m c n budget entryPhase last handle owner := by
  obtain ⟨fuel,request,before,running,earlier,started,key,valid,present,later⟩ := ancestor
  exact ⟨fuel,request,before,running,earlier,started,key,valid,present,.snoc later step⟩

/-- Every evaluating node cell comes from an enclosing activation when the entry table is idle. -/
theorem Reached.owners (actual : Reached g s r e p h m c n budget entryPhase current)
    (valid : NodeValid (caller entryPhase))
    (idle : ∀ handle owner, (caller entryPhase).nodeResults.cells handle ≠ some ⟨owner, .evaluating⟩)
    (handle : Nat) (owner : NodeRequest)
    (present : (caller current).nodeResults.cells handle = some ⟨owner, .evaluating⟩) :
    Ancestor g s r e p h m c n budget entryPhase current handle owner := by
  induction actual with
  | refl => exact False.elim (idle handle owner present)
  | snoc earlier last ih =>
      rcases step_owner last (earlier.valid valid) handle owner present with old | fresh
      · exact ancestor_extend (ih old) last
      · obtain ⟨fuel,request,before,running,firstEq,lastEq,started⟩ := fresh
        cases firstEq
        cases lastEq
        have protocol := earlier.valid valid
        have owned := start_owner request before protocol started
        have runningValid := start_valid request before protocol
        rw [started] at runningValid
        exact ⟨fuel,request,before,running,earlier,started,owned.2,runningValid,owned.1,.refl _⟩

local notation "run" => SourceCurrentOuterActiveAncestry.run

/-- A reached failure propagates through each actual prefix with the same full caller. -/
theorem Step.failed (actual : Step g s r e p h m c n budget first last)
    (failed : run g s r e p h m c n budget last = .failed fault after) :
    run g s r e p h m c n budget first = .failed fault after := by
  cases actual with
  | node_evaluate actual =>
      have actualFailed := erase_failed failed
      simp only [run, nodeCall, actual, actualFailed, Outcome.bind]
  | body_rows actual =>
      have actualFailed := erase_failed failed
      simp only [run, nodeBody, actual, actualFailed, Outcome.bind]
  | rows_edge actual =>
      have actualFailed := erase_failed failed
      simp only [run, rows, actual, actualFailed, Outcome.bind]
  | rows_tail edge children =>
      have actualFailed := erase_failed failed
      simp only [run, rows, edge, children, actualFailed, Outcome.bind]
  | descendants_children actual =>
      have actualFailed := erase_failed failed
      simp only [SourceCurrentAllocatedPartialGraph.prefixState,
        SourceCurrentAllocatedInheritedPrefix.state] at actualFailed
      simp only [run, descendants, actual, actualFailed, Outcome.bind]
  | children_walk live =>
      rename_i combined fuel values before
      simp only [run] at failed ⊢
      cases combined with
      | contradiction => exact False.elim (live rfl)
      | live identity records => simpa only [children] using failed
  | walk_head =>
      have actualFailed := erase_failed failed
      simp only [run, walk, actualFailed, Outcome.bind]
  | walk_tail actual =>
      have actualFailed := erase_failed failed
      simp only [run, walk, actual, actualFailed, Outcome.bind]

/-- Literal failure correspondence holds for the entire derived unfinished prefix. -/
theorem Reached.failed (actual : Reached g s r e p h m c n budget first last)
    (failed : run g s r e p h m c n budget last = .failed fault after) :
    run g s r e p h m c n budget first = .failed fault after := by
  induction actual with
  | refl => exact failed
  | snoc earlier last ih => exact ih (last.failed failed)


end MicroCFTA.SourceCurrentOuterExecutionAncestry
