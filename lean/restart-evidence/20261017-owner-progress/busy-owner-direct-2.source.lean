import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Exact owner cells for outer busy faults

Every bounded mutual worker retains the evaluating owner of each reported
outer busy fault. The proof follows the actual failed execution. It needs
no successful graph, future rank, or idle-table premise. It does not exclude
busy faults or prove general outer completion.
-/
namespace MicroCFTA.SourceCurrentOuterBusyOwners
open InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- A reported busy fault retains its exact evaluating owner at the returned caller. -/
def RetainsOwner : Outcome A width → Prop
  | .failed (.nodeMemo handle .busy) after =>
      ∃ owner, after.nodeResults.cells handle = some ⟨owner, .evaluating⟩
  | .failed (.edgeMemo handle .busy) after =>
      ∃ owner, after.edgeResults.cells handle = some ⟨owner, .evaluating⟩
  | _ => True

private theorem bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (initial : RetainsOwner first) (continued : ∀ value after, RetainsOwner (next value after)) :
    RetainsOwner (first.bind next) := by
  cases first with
  | done value after => exact continued value after
  | failed fault after => simpa only [Outcome.bind, RetainsOwner] using initial

private theorem demand_busy (handle : Nat) (memo : FlatMemoThunk.State Key Request Result)
    (busy : (FlatMemoThunk.demand handle memo).1 = .busy) :
    ∃ owner, memo.cells handle = some ⟨owner, .evaluating⟩ ∧
      (FlatMemoThunk.demand handle memo).2 = memo := by
  cases found : memo.cells handle with
  | none => simp only [FlatMemoThunk.demand, found] at busy; cases busy
  | some cell =>
      cases cell with
      | mk owner status =>
          cases status with
          | suspended | returned result =>
              simp only [FlatMemoThunk.demand, found] at busy
              cases busy
          | evaluating => exact ⟨owner, rfl, by simp only [FlatMemoThunk.demand, found]⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- An actual busy node observation retains the complete caller and its published owner. -/
theorem node_busy (request : NodeRequest) (before after : Caller width) (handle : Nat)
    (observed : beginNode request before = (handle, .busy, after)) :
    after = before ∧ before.nodeResults.table request.key = some handle ∧
      ∃ owner, after.nodeResults.cells handle = some ⟨owner, .evaluating⟩ := by
  cases published : before.nodeResults.table request.key with
  | none =>
      simp [beginNode, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, Cache.put] at observed
  | some selected =>
      have busy : (FlatMemoThunk.demand selected before.nodeResults).1 = .busy := by
        have same := congrArg (fun value => value.2.1) observed
        simpa only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published] using same
      obtain ⟨owner, running, _unchanged⟩ := demand_busy selected before.nodeResults busy
      have equation : beginNode request before = (selected, .busy, before) :=
        beginNode_busy request owner before selected published running
      rw [equation] at observed
      have handles : selected = handle := congrArg Prod.fst observed
      have states : before = after := congrArg (fun value => value.2.2) observed
      subst handle
      subst after
      exact ⟨rfl, rfl, owner, running⟩

/-- An actual busy edge observation retains its own published owner and the complete caller. -/
theorem edge_busy (request : EdgeRequest) (before after : Caller width) (handle : Nat)
    (observed : beginEdge request before = (handle, .busy, after)) :
    after = before ∧ before.edgeResults.table request.key = some handle ∧
      ∃ owner, after.edgeResults.cells handle = some ⟨owner, .evaluating⟩ := by
  cases published : before.edgeResults.table request.key with
  | none =>
      simp [beginEdge, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, Cache.put] at observed
  | some selected =>
      have busy : (FlatMemoThunk.demand selected before.edgeResults).1 = .busy := by
        have same := congrArg (fun value => value.2.1) observed
        simpa only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published] using same
      obtain ⟨owner, running, _unchanged⟩ := demand_busy selected before.edgeResults busy
      have equation : beginEdge request before = (selected, .busy, before) :=
        beginEdge_busy request owner before selected published running
      rw [equation] at observed
      have handles : selected = handle := congrArg Prod.fst observed
      have states : before = after := congrArg (fun value => value.2.2) observed
      subst handle
      subst after
      exact ⟨rfl, rfl, owner, running⟩

private theorem edgeBody_owner (fuel g s r e p h m c n budget : Nat)
    (request : EdgeRequest) (before : Caller width) :
    RetainsOwner (edgeBody fuel g s r e p h m c n budget request before) := by
  unfold edgeBody
  split <;> trivial

private theorem edgeCall_owner (fuel g s r e p h m c n budget : Nat)
    (request : EdgeRequest) (before : Caller width) :
    RetainsOwner (edgeCall fuel g s r e p h m c n budget request before) := by
  rcases observed : beginEdge request before with ⟨handle, action, after⟩
  cases action with
  | ready value | absent => simp only [edgeCall, observed, RetainsOwner]
  | busy => simpa only [edgeCall, observed, RetainsOwner] using
      (edge_busy request before after handle observed).2.2
  | evaluate owner =>
      simp only [edgeCall, observed]
      exact bind _ _ (edgeBody_owner _ _ _ _ _ _ _ _ _ _ _ _ _) (by intros; trivial)

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width),
    RetainsOwner (nodeCall fuel g s r e p h m c n budget request before)
private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width),
    RetainsOwner (nodeBody fuel g s r e p h m c n budget request before)
private def RowsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width),
    RetainsOwner (rows fuel g s r e p h m c n budget inherited values before)
private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited edge (before : Caller width),
    RetainsOwner (descendants fuel g s r e p h m c n budget inherited edge before)
private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width),
    RetainsOwner (children fuel g s r e p h m c n budget inherited values before)
private def WalkAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited index values (before : Caller width),
    RetainsOwner (walk fuel g s r e p h m c n budget inherited index values before)

private theorem all_owners (fuel : Nat) :
    NodeCallAt (width := width) fuel ∧ NodeBodyAt (width := width) fuel ∧
      RowsAt (width := width) fuel ∧ DescendantsAt (width := width) fuel ∧
      ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | h fuel ih =>
      have walkAt : WalkAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited index values before
        cases values with
        | nil => trivial
        | cons value rest =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [walk]
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).1 _ _ _ _ _ _ _ _ _ _ _ _)
                intro result middle
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _)
                intros
                trivial
      have childrenAt : ChildrenAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before
        cases inherited with
        | contradiction => trivial
        | live identity records => exact walkAt _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have descendantsAt : DescendantsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited edge before
        unfold descendants
        split
        · trivial
        · trivial
        · apply bind _ _ (childrenAt _ _ _ _ _ _ _ _ _ _ _ _ _)
          intros
          trivial
      have rowsAt : RowsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before
        cases values with
        | nil => trivial
        | cons value rest =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [rows]
                apply bind _ _ (edgeCall_owner _ _ _ _ _ _ _ _ _ _ _ _ _)
                intro result middle
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _)
                intro narrowed after
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _)
                intros
                trivial
      have bodyAt : NodeBodyAt (width := width) fuel := by
        intro g s r e p h m c n budget request before
        rcases request with ⟨inherited, value⟩
        cases value with
        | empty | union | reference => trivial
        | mu entry body depth ordinary =>
            unfold nodeBody
            split <;> trivial
        | node entry originals depth free =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [nodeBody]
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _)
                intros
                trivial
      have callAt : NodeCallAt (width := width) fuel := by
        intro g s r e p h m c n budget request before
        rcases observed : beginNode request before with ⟨handle, action, after⟩
        cases action with
        | ready value | absent => simp only [nodeCall, observed, RetainsOwner]
        | busy => simpa only [nodeCall, observed, RetainsOwner] using
            (node_busy request before after handle observed).2.2
        | evaluate owner =>
            simp only [nodeCall, observed]
            exact bind _ _ (bodyAt _ _ _ _ _ _ _ _ _ _ _ _) (by intros; trivial)
      exact ⟨callAt, bodyAt, rowsAt, descendantsAt, childrenAt, walkAt⟩

/-- Every literal node call retains the owner of any reported outer busy fault. -/
theorem node_call (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller width) :
    RetainsOwner (nodeCall fuel g s r e p h m c n budget request before) :=
  (all_owners fuel).1 _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal node body retains the owner of any propagated outer busy fault. -/
theorem node_body (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller width) :
    RetainsOwner (nodeBody fuel g s r e p h m c n budget request before) :=
  (all_owners fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal edge call retains the owner of any reported outer busy fault. -/
theorem edge_call (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width) :
    RetainsOwner (edgeCall fuel g s r e p h m c n budget request before) :=
  edgeCall_owner _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal row pass retains the owner of any propagated outer busy fault. -/
theorem row_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (values : List Edge) (before : Caller width) :
    RetainsOwner (rows fuel g s r e p h m c n budget inherited values before) :=
  (all_owners fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal descendant pass retains the owner of any propagated outer busy fault. -/
theorem descendant_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (value : Edge) (before : Caller width) :
    RetainsOwner (descendants fuel g s r e p h m c n budget inherited value before) :=
  (all_owners fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal child pass retains the owner of any propagated outer busy fault. -/
theorem child_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (values : List Node) (before : Caller width) :
    RetainsOwner (children fuel g s r e p h m c n budget inherited values before) :=
  (all_owners fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Every literal indexed walk retains the owner of any propagated outer busy fault. -/
theorem indexed_walk (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (index : Nat) (values : List Node) (before : Caller width) :
    RetainsOwner (walk fuel g s r e p h m c n budget inherited index values before) :=
  (all_owners fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _

end MicroCFTA.SourceCurrentOuterBusyOwners
