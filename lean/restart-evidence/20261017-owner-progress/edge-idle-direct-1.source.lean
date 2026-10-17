import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.FlatMemoThunkRunningBefore

/-!
# No new busy edge fault from an edge-idle outer caller

The parent edge body makes no outer recursive request. A successful edge
call finishes its owner before descendant traversal starts. Failed bodies
propagate immediately. Every bounded worker therefore preserves edge idle
on success and cannot report a busy edge fault from an edge-idle entry.
Node owners may remain evaluating. This result does not prove completion.
-/
namespace MicroCFTA.SourceCurrentOuterEdgeIdle
open InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- An edge-idle caller has no evaluating cell in its edge result family. -/
def EdgeIdle (state : Caller width) : Prop :=
  ∀ handle owner, state.edgeResults.cells handle ≠ some ⟨owner, .evaluating⟩

/-- Successful outcomes retain edge idle; failed outcomes exclude a busy edge diagnostic. -/
def Safe : Outcome A width → Prop
  | .done _ after => EdgeIdle after
  | .failed (.edgeMemo _ .busy) _ => False
  | .failed _ _ => True

/-- Initial outer tables are edge-idle for every supplied lower checked state. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    EdgeIdle (SourceCurrentAllocatedPartialState.initial checked merge fourth) := by
  intro handle owner impossible
  cases impossible

private theorem bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (safe : Safe first) (continued : ∀ value after, EdgeIdle after → Safe (next value after)) :
    Safe (first.bind next) := by
  cases first with
  | done value after => exact continued value after safe
  | failed fault after => exact safe

private theorem edge_other (request : EdgeRequest) (before : Caller width) (other : Nat) (owner : EdgeRequest)
    (different : other ≠ (beginEdge request before).1)
    (found : (beginEdge request before).2.2.edgeResults.cells other = some ⟨owner, .evaluating⟩) :
    before.edgeResults.cells other = some ⟨owner, .evaluating⟩ :=
  FlatMemoThunk.lookup_running_before request.key request before.edgeResults other owner
    (FlatMemoThunk.demand_running_before_other _ other _ owner different found)

private theorem ready_idle (request : EdgeRequest) (before : Caller width)
    (idle : EdgeIdle before) (value : Edge)
    (ready : (beginEdge request before).2.1 = .ready value) : EdgeIdle (beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have actual : FlatMemoThunk.demand published.1 published.2 =
      (.ready value, (FlatMemoThunk.demand published.1 published.2).2) := Prod.ext ready rfl
  obtain ⟨_, _, unchanged⟩ := FlatMemoThunk.demand_ready_original published.1 published.2 value _ actual
  intro handle owner found
  have earlier : published.2.cells handle = some ⟨owner, .evaluating⟩ :=
    (congrArg (fun memo => memo.cells handle) unchanged).symm.trans found
  exact idle handle owner (FlatMemoThunk.lookup_running_before request.key request before.edgeResults handle owner earlier)

private theorem busy_impossible (request : EdgeRequest) (before : Caller width)
    (idle : EdgeIdle before) (busy : (beginEdge request before).2.1 = .busy) : False := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have actual : FlatMemoThunk.demand published.1 published.2 =
      (.busy, (FlatMemoThunk.demand published.1 published.2).2) := Prod.ext busy rfl
  obtain ⟨owner, found, _⟩ := FlatMemoThunk.demand_busy_before published.1 published.2 _ actual
  exact idle published.1 owner
    (FlatMemoThunk.lookup_running_before request.key request before.edgeResults published.1 owner found)

private theorem finished_idle (request : EdgeRequest) (before : Caller width)
    (idle : EdgeIdle before) (result : Edge) (checked : SourceEqualityNativeDemand.State width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    EdgeIdle (finishEdge (beginEdge request before).1 result
      (advance (beginEdge request before).2.2 checked fourth merge)) := by
  intro handle owner found
  have different : handle ≠ (beginEdge request before).1 := by
    intro same
    subst handle
    exact FlatMemoThunk.finish_not_running _ result (beginEdge request before).2.2.edgeResults owner found
  exact idle handle owner (edge_other request before handle owner different
    (FlatMemoThunk.finish_running_before _ result (beginEdge request before).2.2.edgeResults handle owner found))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem edgeBody_safe (fuel g s r e p h m c n budget : Nat)
    (request : EdgeRequest) (before : Caller width) (idle : EdgeIdle before) :
    Safe (edgeBody fuel g s r e p h m c n budget request before) := by
  unfold edgeBody
  split
  · exact idle
  · trivial

private theorem edgeCall_safe (fuel g s r e p h m c n budget : Nat)
    (request : EdgeRequest) (before : Caller width) (idle : EdgeIdle before) :
    Safe (edgeCall fuel g s r e p h m c n budget request before) := by
  rcases observed : beginEdge request before with ⟨handle, action, after⟩
  cases action with
  | ready value =>
      have ready := ready_idle request before idle value (congrArg (fun result => result.2.1) observed)
      simpa only [edgeCall, observed, Safe] using ready
  | busy => exact (busy_impossible request before idle (congrArg (fun result => result.2.1) observed)).elim
  | absent => simp only [edgeCall, observed, Safe]
  | evaluate owner =>
      simp only [edgeCall, observed]
      unfold edgeBody
      split
      · simpa only [Outcome.bind, Safe, observed] using finished_idle request before idle _ _ _ _
      · trivial

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width), EdgeIdle before →
    Safe (nodeCall fuel g s r e p h m c n budget request before)
private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width), EdgeIdle before →
    Safe (nodeBody fuel g s r e p h m c n budget request before)
private def RowsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width), EdgeIdle before →
    Safe (rows fuel g s r e p h m c n budget inherited values before)
private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited edge (before : Caller width), EdgeIdle before →
    Safe (descendants fuel g s r e p h m c n budget inherited edge before)
private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width), EdgeIdle before →
    Safe (children fuel g s r e p h m c n budget inherited values before)
private def WalkAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited index values (before : Caller width), EdgeIdle before →
    Safe (walk fuel g s r e p h m c n budget inherited index values before)

private theorem all_safe (fuel : Nat) :
    NodeCallAt (width := width) fuel ∧ NodeBodyAt (width := width) fuel ∧
      RowsAt (width := width) fuel ∧ DescendantsAt (width := width) fuel ∧
      ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walkAt : WalkAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited index values before idle
        cases values with
        | nil => exact idle
        | cons value rest =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [walk]
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).1 _ _ _ _ _ _ _ _ _ _ _ _ idle)
                intro result middle middleIdle
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ middleIdle)
                intro results after afterIdle
                exact afterIdle
      have childrenAt : ChildrenAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before idle
        cases inherited with
        | contradiction => exact idle
        | live identity records => exact walkAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ idle
      have descendantsAt : DescendantsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited edge before idle
        simp only [descendants]
        split
        · trivial
        · trivial
        · apply bind _ _ (childrenAt _ _ _ _ _ _ _ _ _ _ _ _ _ idle)
          intro results after afterIdle
          exact afterIdle
      have rowsAt : RowsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before idle
        cases values with
        | nil => exact idle
        | cons value rest =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [rows]
                apply bind _ _ (edgeCall_safe _ _ _ _ _ _ _ _ _ _ _ _ _ idle)
                intro narrowed middle middleIdle
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ middleIdle)
                intro result after afterIdle
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ afterIdle)
                intro results final finalIdle
                exact finalIdle
      have bodyAt : NodeBodyAt (width := width) fuel := by
        intro g s r e p h m c n budget request before idle
        rcases request with ⟨inherited, value⟩
        cases value with
        | empty | union => exact idle
        | reference => trivial
        | mu entry body depth ordinary =>
            simp only [nodeBody]
            split
            · exact idle
            · trivial
        | node entry originals depth free =>
            cases fuel with
            | zero => trivial
            | succ fuel =>
                simp only [nodeBody]
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ idle)
                intro results after afterIdle
                exact afterIdle
      have callAt : NodeCallAt (width := width) fuel := by
        intro g s r e p h m c n budget request before idle
        rcases observed : beginNode request before with ⟨handle, action, after⟩
        have afterIdle : EdgeIdle after := by
          have parts := beginNode_components request before
          rw [observed] at parts
          simpa only [EdgeIdle, parts.2.2.2] using idle
        cases action with
        | ready value => simpa only [nodeCall, observed, Safe] using afterIdle
        | busy | absent => simp only [nodeCall, observed, Safe]
        | evaluate owner =>
            simp only [nodeCall, observed]
            apply bind _ _ (bodyAt _ _ _ _ _ _ _ _ _ _ _ _ afterIdle)
            intro result middle middleIdle
            exact middleIdle
      exact ⟨callAt, bodyAt, rowsAt, descendantsAt, childrenAt, walkAt⟩

/-- Every bounded node call preserves edge idle on success and excludes a busy edge failure. -/
theorem node_call (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) (idle : EdgeIdle before) :
    Safe (nodeCall fuel g s r e p h m c n budget request before) :=
  (all_safe fuel).1 _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- Every bounded node body has the same edge-family property. -/
theorem node_body (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) (idle : EdgeIdle before) :
    Safe (nodeBody fuel g s r e p h m c n budget request before) :=
  (all_safe fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- A complete edge call finishes its selected edge before returning to descendants. -/
theorem edge_call (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (idle : EdgeIdle before) :
    Safe (edgeCall fuel g s r e p h m c n budget request before) := edgeCall_safe _ _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- The actual parent edge body cannot introduce an outer busy diagnostic. -/
theorem edge_body (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (idle : EdgeIdle before) :
    Safe (edgeBody fuel g s r e p h m c n budget request before) := edgeBody_safe _ _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- Ordered rows retain the edge-family property through their actual descendant calls. -/
theorem row_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (values : List Edge) (before : Caller width) (idle : EdgeIdle before) :
    Safe (rows fuel g s r e p h m c n budget inherited values before) :=
  (all_safe fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- Actual inherited prefixes and descendant reconstruction retain the property. -/
theorem descendant_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (value : Edge) (before : Caller width) (idle : EdgeIdle before) :
    Safe (descendants fuel g s r e p h m c n budget inherited value before) :=
  (all_safe fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- Both contradictory child erasure and live indexed traversal retain the property. -/
theorem child_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (values : List Node) (before : Caller width) (idle : EdgeIdle before) :
    Safe (children fuel g s r e p h m c n budget inherited values before) :=
  (all_safe fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ idle

/-- Every indexed walk excludes a busy edge failure from its edge-idle entry. -/
theorem indexed_walk (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (index : Nat) (values : List Node) (before : Caller width) (idle : EdgeIdle before) :
    Safe (walk fuel g s r e p h m c n budget inherited index values before) :=
  (all_safe fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ idle

end MicroCFTA.SourceCurrentOuterEdgeIdle
