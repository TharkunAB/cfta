import MicroCFTA.SourceCurrentAllocatedPartialChecks
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual
import MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion

/-!
# Composition of reached checks for actual outer constructors

Each constructor combines only the checks of its actual children.
An edge-body leaf requires its reached machine-range plan. These
proofs add no semantic, physical, or future-completion premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialChecksComposition
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialState (beginNode beginEdge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
  {width budget : Nat}


private inductive Input (width : Nat) where
  | nodeCall (request : NodeReq) (before : Caller width)
  | nodeBody (request : NodeReq) (before : Caller width)
  | edgeCall (request : EdgeReq) (before : Caller width)
  | edgeBody (request : EdgeReq) (before : Caller width)
  | rows (inherited : EqValue) (values : List (EdgeValue Symbol Guard)) (before : Caller width)
  | descendants (inherited : EqValue) (value : EdgeValue Symbol Guard) (before : Caller width)
  | children (combined : EqValue) (values : List (Value Symbol Guard)) (before : Caller width)
  | walk (combined : EqValue) (index : Nat) (values : List (Value Symbol Guard)) (before : Caller width)

private def input : Trace width budget → Input width
  | .nodeCall request before _ _ _ => .nodeCall request before
  | .nodeBody request before _ _ _ => .nodeBody request before
  | .edgeCall request before _ _ _ => .edgeCall request before
  | .edgeBody request before _ _ _ => .edgeBody request before
  | .rows inherited values before _ _ _ => .rows inherited values before
  | .descendants inherited value before _ _ _ => .descendants inherited value before
  | .children combined values before _ _ _ => .children combined values before
  | .walk combined index values before _ _ _ => .walk combined index values before

private theorem compose (top : Trace width budget)
    (root : ∀ request before result after (actual : EdgeBody budget request before result after),
      top = edgeBodyTrace actual → SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before)
    (children : ∀ child, Direct top child → Checks child) : Checks top := by
  intro request before result after actual reached
  cases reached with
  | refl => exact root request before result after actual rfl
  | step direct rest => exact children _ direct request before result after actual rest


omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem stable_unique
    {A : Type} {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      SourceCurrentAllocatedPartialWorker.Outcome A width}
    {left right : A} {after later : Caller width}
    (one : SourceCurrentAllocatedPartialWorkerCompletion.StableRun evaluation left after)
    (two : SourceCurrentAllocatedPartialWorkerCompletion.StableRun evaluation right later) :
    left = right ∧ after = later := by
  obtain ⟨f, g, s, r, e, p, h, m, c, n, first⟩ := one
  obtain ⟨F, G, S, R, E, P, H, M, C, N, second⟩ := two
  have a := first (max f F) (max g G) (max s S) (max r R) (max e E)
    (max p P) (max h H) (max m M) (max c C) (max n N)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have b := second (max f F) (max g G) (max s S) (max r R) (max e E)
    (max p P) (max h H) (max m M) (max c C) (max n N)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact SourceCurrentAllocatedPartialWorker.Outcome.done.inj (a.symm.trans b)

open SourceCurrentAllocatedPartialWorkerCompletion

/-- A returned node hit reaches no edge-body leaf. -/
theorem node_hit {request : NodeReq} {before running : Caller width} {result : Value Symbol Guard} {handle : Nat}
    (started : beginNode request before = (handle, (.ready result, running))) :
    Checks (nodeCallTrace (NodeCall.hit (budget := budget) started)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct with
    | node_evaluate other body =>
      rw [started] at other
      cases other


/-- An evaluating node reaches exactly its actual body checks. -/
theorem node_evaluate {request original : NodeReq} {before running middle : Caller width}
    {result : Value Symbol Guard} {handle : Nat}
    (started : beginNode request before = (handle, (.evaluate original, running)))
    (body : NodeBody budget original running result middle) (checks : Checks (nodeBodyTrace body)) :
    Checks (nodeCallTrace (NodeCall.evaluate started body)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    generalize origin : nodeCallTrace (NodeCall.evaluate started body) = top at direct
    have inputs : input top = .nodeCall request before := by rw [← origin]; rfl
    cases direct <;> cases inputs
    rename_i otherBody other
    rw [started] at other
    cases other
    obtain ⟨sameResult, sameState⟩ := stable_unique (nodeBody_complete body) (nodeBody_complete otherBody)
    cases sameResult
    cases sameState
    exact checks

/-- An empty body reaches no edge-body leaf. -/
theorem empty {inherited : EqValue} {before : Caller width} :
    Checks (nodeBodyTrace (NodeBody.empty (budget := budget) (inherited := inherited) (before := before))) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- An unchanged union body reaches no edge-body leaf. -/
theorem union {inherited : EqValue} {before : Caller width}
    {entry : Interned InternedBinderProtocol.NodeKey} {members : List (Value Symbol Guard)}
    {depth : Nat} {free : List InternedBinderProtocol.Reference} :
    Checks (nodeBodyTrace (NodeBody.union (budget := budget) (inherited := inherited) (before := before)
      (entry := entry) (members := members) (depth := depth) (free := free))) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- A completed literal binder reconstruction reaches no edge-body leaf. -/
theorem binder {inherited : EqValue} {before : Caller width}
    {entry : Interned InternedBinderProtocol.NodeKey} {body depth ordinary result : Value Symbol Guard}
    {heap : State Symbol Guard}
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap =
      .done result heap) :
    Checks (nodeBodyTrace (NodeBody.binder (budget := budget) (inherited := inherited) actual)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- An ordinary body composes the checks of its ordered actual rows. -/
theorem ordinary {inherited : EqValue} {before middle : Caller width}
    {edges results : List (EdgeValue Symbol Guard)} {entry : Interned InternedBinderProtocol.NodeKey}
    {depth : Nat} {free : List InternedBinderProtocol.Reference}
    (actual : Rows budget inherited edges before results middle) (checks : Checks (rowsTrace actual)) :
    Checks (nodeBodyTrace (NodeBody.ordinary (entry := entry) (depth := depth) (free := free) actual)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    generalize origin : nodeBodyTrace (NodeBody.ordinary (entry := entry) (depth := depth) (free := free) actual) = top at direct
    have inputs : input top = .nodeBody ⟨inherited, .node entry edges depth free⟩ before := by rw [← origin]; rfl
    cases direct <;> cases inputs
    rename_i other
    obtain ⟨sameResults, sameState⟩ := stable_unique (rows_complete actual) (rows_complete other)
    cases sameResults
    cases sameState
    exact checks

/-- A returned edge hit reaches no edge-body leaf. -/
theorem edge_hit {request : EdgeReq} {before running : Caller width} {result : EdgeValue Symbol Guard} {handle : Nat}
    (started : beginEdge request before = (handle, (.ready result, running))) :
    Checks (edgeCallTrace (EdgeCall.hit (budget := budget) started)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct with
    | edge_evaluate other body =>
      rw [started] at other
      cases other

/-- An evaluating edge composes its exact body leaf checks. -/
theorem edge_evaluate {request original : EdgeReq} {before running middle : Caller width}
    {result : EdgeValue Symbol Guard} {handle : Nat}
    (started : beginEdge request before = (handle, (.evaluate original, running)))
    (body : EdgeBody budget original running result middle) (checks : Checks (edgeBodyTrace body)) :
    Checks (edgeCallTrace (EdgeCall.evaluate started body)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    generalize origin : edgeCallTrace (EdgeCall.evaluate started body) = top at direct
    have inputs : input top = .edgeCall request before := by rw [← origin]; rfl
    cases direct <;> cases inputs
    rename_i otherBody other
    rw [started] at other
    cases other
    intro request before result after actual reached
    cases reached with
    | refl => exact checks.edge_body
    | step direct _ => cases direct

/-- An edge-body leaf requires only its reached machine-range plan. -/
theorem edge_body {request : EdgeReq} {before after : Caller width} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after)
    (ranges : SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before) : Checks (edgeBodyTrace actual) := by
  apply compose
  · intro request before result after actual same
    cases same
    exact ranges
  · intro child direct
    cases direct

/-- Empty ordered rows reach no edge-body leaf. -/
theorem rows_nil {inherited : EqValue} {before : Caller width} :
    Checks (rowsTrace (Rows.nil (budget := budget) (inherited := inherited) (before := before))) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- A source row composes edge, returned-edge descendants, and suffix checks. -/
theorem rows_cons {inherited : EqValue} {original : EdgeValue Symbol Guard}
    {originals results : List (EdgeValue Symbol Guard)} {narrowed result : EdgeValue Symbol Guard}
    {before middle afterChildren after : Caller width}
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result afterChildren)
    (rest : Rows budget inherited originals afterChildren results after)
    (edgeChecks : Checks (edgeCallTrace edge)) (childrenChecks : Checks (descendantsTrace children))
    (restChecks : Checks (rowsTrace rest)) : Checks (rowsTrace (Rows.cons edge children rest)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct with
    | rows_edge other otherChildren otherRest =>
      obtain ⟨rfl, rfl⟩ := stable_unique (edgeCall_complete edge) (edgeCall_complete other)
      exact edgeChecks
    | rows_descendants other otherChildren otherRest =>
      obtain ⟨rfl, rfl⟩ := stable_unique (edgeCall_complete edge) (edgeCall_complete other)
      have sameState := (stable_unique (descendants_complete children) (descendants_complete otherChildren)).2
      cases sameState
      exact childrenChecks
    | rows_tail other otherChildren otherRest =>
      obtain ⟨rfl, rfl⟩ := stable_unique (edgeCall_complete edge) (edgeCall_complete other)
      have sameState := (stable_unique (descendants_complete children) (descendants_complete otherChildren)).2
      cases sameState
      exact restChecks

/-- The actual inherited prefix adds no leaf beyond its child branch. -/
theorem descendants_run {inherited payload : EqValue} {edge : EdgeValue Symbol Guard}
    {before middle : Caller width} {results : List (Value Symbol Guard)}
    (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 =
      .ok (some payload))
    (actual : Children budget payload edge.children (prefixState before edge inherited) results middle)
    (checks : Checks (childrenTrace actual)) :
    Checks (descendantsTrace (Descendants.run combined actual)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    generalize origin : descendantsTrace (Descendants.run combined actual) = top at direct
    have inputs : input top = .descendants inherited edge before := by rw [← origin]; rfl
    cases direct <;> cases inputs
    rename_i other otherChildren
    have same := combined.symm.trans other
    cases same
    obtain ⟨sameResults, sameState⟩ := stable_unique (children_complete actual) (children_complete otherChildren)
    cases sameResults
    cases sameState
    exact checks

/-- Contradiction reaches no child request or edge-body leaf. -/
theorem children_contradiction {values : List (Value Symbol Guard)} {before : Caller width} :
    Checks (childrenTrace (Children.contradiction (budget := budget) (values := values) (before := before))) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- A live child branch composes its actual indexed walk checks. -/
theorem children_live {identity : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (actual : Walk budget (.live identity records) 0 values before results after)
    (checks : Checks (walkTrace actual)) : Checks (childrenTrace (Children.live actual)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct with
    | children_walk other => exact checks

/-- An empty indexed walk reaches no edge-body leaf. -/
theorem walk_nil {combined : EqValue} {index : Nat} {before : Caller width} :
    Checks (walkTrace (Walk.nil (budget := budget) (combined := combined) (index := index) (before := before))) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct

/-- An indexed walk composes its actual head request and suffix checks. -/
theorem walk_cons {combined : EqValue} {index : Nat} {value result : Value Symbol Guard}
    {values results : List (Value Symbol Guard)} {before middle after : Caller width}
    (head : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle)
    (tail : Walk budget combined (index + 1) values middle results after)
    (headChecks : Checks (nodeCallTrace head)) (tailChecks : Checks (walkTrace tail)) :
    Checks (walkTrace (Walk.cons head tail)) := by
  apply compose
  · intro request before result after actual same
    cases same
  · intro child direct
    cases direct with
    | walk_head other otherTail =>
      have sameState := (stable_unique (nodeCall_complete head) (nodeCall_complete other)).2
      cases sameState
      exact headChecks
    | walk_tail other otherTail =>
      have sameState := (stable_unique (nodeCall_complete head) (nodeCall_complete other)).2
      cases sameState
      exact tailChecks

/-- The finite local machine plan implies only the reached actual Scan checks. -/
theorem resident_ranges {request : EdgeReq} {before : Caller width}
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before) :
    SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before := by
  intro live loaded found
  exact SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (ranges live loaded found)

end MicroCFTA.SourceCurrentAllocatedPartialChecksComposition
