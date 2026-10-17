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
  exact ⟨same ▸ valid, fun _ _ found => same ▸ found, fun _ _ found => same ▸ found⟩

private theorem frame_trans {before middle after : Caller width}
    (first : Frame before middle) (last : Frame middle after) : Frame before after :=
  ⟨last.valid, first.forward.trans last.forward, last.reverse.trans first.reverse⟩

private def Completed (before : Caller width) : Outcome A width → Prop
  | .done _ after => Frame before after
  | .failed .. => True

private theorem completed_bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (checked : Completed before first)
    (later : ∀ value middle, Frame before middle → Completed before (next value middle)) :
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

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

private theorem edge_nodes (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width) :
    (edgeCall fuel g s r e p h m c n budget request before).state.nodeResults = before.nodeResults := by
  unfold edgeCall
  split
  · rfl
  · unfold edgeBody
    split <;> rfl
  · rfl
  · rfl

private theorem edge_no_busy (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (failed : edgeCall fuel g s r e p h m c n budget request before = .failed (.nodeMemo handle .busy) after) : False := by
  unfold edgeCall at failed
  split at failed
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
      | nil => exact frame_same valid rfl
      | cons value rest =>
        cases fuel with
        | zero => trivial
        | succ fuel =>
          simp only [walk]
          have head := (ih fuel (Nat.lt_succ_self _)).1 g s r e p h m c n budget
            ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1,value⟩
            (SourceCurrentAllocatedPartialGraph.descend before combined index).2 valid
          apply completed_bind _ _ head
          intro result middle first
          have tail := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 g s r e p h m c n budget combined (index+1) rest middle first.valid
          apply completed_bind _ _ (completed_after first tail)
          intro results after last
          exact last
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget combined values before valid
      cases combined with
      | contradiction => exact frame_same valid rfl
      | live identity records => exact walkAt g s r e p h m c n budget (.live identity records) 0 values before valid
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before valid
      simp only [descendants]
      split
      · trivial
      · trivial
      · rename_i combined _
        apply completed_bind _ _ (childrenAt g s r e p h m c n budget combined value.children _ valid)
        intro results after first
        exact ⟨first.valid,first.forward,first.reverse⟩
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before valid
      cases values with
      | nil => exact frame_same valid rfl
      | cons value rest =>
        cases fuel with
        | zero => trivial
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
      | empty | union => exact frame_same valid rfl
      | reference => trivial
      | mu entry body depth ordinary =>
        simp only [nodeBody]
        split
        · exact frame_same valid rfl
        · trivial
      | node entry original depth free =>
        cases fuel with
        | zero => trivial
        | succ fuel =>
          simp only [nodeBody]
          apply completed_bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n budget inherited original before valid)
          intro result after first
          exact ⟨first.valid,first.forward,first.reverse⟩
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before valid
      rcases started : beginNode request before with ⟨handle,action,running⟩
      cases action with
      | ready result => exact hit_frame request before valid started
      | absent | busy => trivial
      | evaluate original =>
        have checked := start_valid request before valid
        rw [started] at checked
        simp only [nodeCall,started]
        apply completed_bind _ _ (bodyAt g s r e p h m c n budget original running checked)
        intro result middle first
        exact evaluate_frame request before valid started first result
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

end MicroCFTA.SourceCurrentOuterExecutionAncestry
