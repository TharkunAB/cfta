import MicroCFTA.SourceCurrentAllocatedPartialEdgeActual

/-!
# Reached word checks for the current mutual caller graph

Each trace wrapper retains its physical indices as data. Direct paths
follow actual completed graph constructors. Checks require only the Scan
word-range plan at reached edge bodies. They contain no result language,
future invariant, or completion premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialChecks
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialState (beginNode beginEdge finishNode finishEdge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Physical graph indices are data fields, independent of their proposition-valued certificate. -/
inductive Trace (width budget : Nat) : Type 1 where
  | nodeCall (request : NodeReq) (before : Caller width) (result : Value Symbol Guard) (after : Caller width)
      (actual : NodeCall budget request before result after) : Trace width budget
  | nodeBody (request : NodeReq) (before : Caller width) (result : Value Symbol Guard) (after : Caller width)
      (actual : NodeBody budget request before result after) : Trace width budget
  | edgeCall (request : EdgeReq) (before : Caller width) (result : EdgeValue Symbol Guard) (after : Caller width)
      (actual : EdgeCall budget request before result after) : Trace width budget
  | edgeBody (request : EdgeReq) (before : Caller width) (result : EdgeValue Symbol Guard) (after : Caller width)
      (actual : EdgeBody budget request before result after) : Trace width budget
  | rows (inherited : EqValue) (values : List (EdgeValue Symbol Guard)) (before : Caller width)
      (results : List (EdgeValue Symbol Guard)) (after : Caller width)
      (actual : Rows budget inherited values before results after) : Trace width budget
  | descendants (inherited : EqValue) (value : EdgeValue Symbol Guard) (before : Caller width)
      (result : EdgeValue Symbol Guard) (after : Caller width)
      (actual : Descendants budget inherited value before result after) : Trace width budget
  | children (combined : EqValue) (values : List (Value Symbol Guard)) (before : Caller width)
      (results : List (Value Symbol Guard)) (after : Caller width)
      (actual : Children budget combined values before results after) : Trace width budget
  | walk (combined : EqValue) (index : Nat) (values : List (Value Symbol Guard)) (before : Caller width)
      (results : List (Value Symbol Guard)) (after : Caller width)
      (actual : Walk budget combined index values before results after) : Trace width budget

variable {width budget : Nat}

/-- Construct a node-call wrapper with inferred physical indices. -/
abbrev nodeCallTrace {request result} {before after : Caller width} (actual : NodeCall budget request before result after) : Trace width budget :=
  .nodeCall request before result after actual

/-- Construct a node-body wrapper with inferred physical indices. -/
abbrev nodeBodyTrace {request result} {before after : Caller width} (actual : NodeBody budget request before result after) : Trace width budget :=
  .nodeBody request before result after actual

/-- Construct an edge-call wrapper with inferred physical indices. -/
abbrev edgeCallTrace {request result} {before after : Caller width} (actual : EdgeCall budget request before result after) : Trace width budget :=
  .edgeCall request before result after actual

/-- Construct an edge-body wrapper with inferred physical indices. -/
abbrev edgeBodyTrace {request result} {before after : Caller width} (actual : EdgeBody budget request before result after) : Trace width budget :=
  .edgeBody request before result after actual

/-- Construct a row wrapper with inferred physical indices. -/
abbrev rowsTrace {inherited values results} {before after : Caller width} (actual : Rows budget inherited values before results after) : Trace width budget :=
  .rows inherited values before results after actual

/-- Construct a descendants wrapper with inferred physical indices. -/
abbrev descendantsTrace {inherited value result} {before after : Caller width} (actual : Descendants budget inherited value before result after) : Trace width budget :=
  .descendants inherited value before result after actual

/-- Construct a child-branch wrapper with inferred physical indices. -/
abbrev childrenTrace {combined values results} {before after : Caller width} (actual : Children budget combined values before results after) : Trace width budget :=
  .children combined values before results after actual

/-- Construct an indexed walk wrapper with inferred physical indices. -/
abbrev walkTrace {combined index values results} {before after : Caller width} (actual : Walk budget combined index values before results after) : Trace width budget :=
  .walk combined index values before results after actual

/-- Each direct path names one actual child of the supplied completed constructor. -/
inductive Direct : Trace width budget → Trace width budget → Prop where
  | node_evaluate {request original before running result middle handle}
      (started : beginNode request before = (handle, (.evaluate original, running)))
      (body : NodeBody budget original running result middle) :
      Direct (nodeCallTrace (.evaluate started body)) (nodeBodyTrace body)
  | node_ordinary {inherited edges before results middle}
      {entry : Interned InternedBinderProtocol.NodeKey} {depth : Nat} {free : List InternedBinderProtocol.Reference}
      (rows : Rows budget inherited edges before results middle) :
      Direct (nodeBodyTrace (NodeBody.ordinary (entry := entry) (depth := depth) (free := free) rows)) (rowsTrace rows)
  | edge_evaluate {request original before running result middle handle}
      (started : beginEdge request before = (handle, (.evaluate original, running)))
      (body : EdgeBody budget original running result middle) :
      Direct (edgeCallTrace (.evaluate started body)) (edgeBodyTrace body)
  | rows_edge {inherited original originals before narrowed middle result afterChildren results after}
      (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : Descendants budget inherited narrowed middle result afterChildren)
      (rest : Rows budget inherited originals afterChildren results after) :
      Direct (rowsTrace (.cons edge children rest)) (edgeCallTrace edge)
  | rows_descendants {inherited original originals before narrowed middle result afterChildren results after}
      (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : Descendants budget inherited narrowed middle result afterChildren)
      (rest : Rows budget inherited originals afterChildren results after) :
      Direct (rowsTrace (.cons edge children rest)) (descendantsTrace children)
  | rows_tail {inherited original originals before narrowed middle result afterChildren results after}
      (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : Descendants budget inherited narrowed middle result afterChildren)
      (rest : Rows budget inherited originals afterChildren results after) :
      Direct (rowsTrace (.cons edge children rest)) (rowsTrace rest)
  | descendants_children {edge inherited before payload results middle}
      (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some payload))
      (children : Children budget payload edge.children (prefixState before edge inherited) results middle) :
      Direct (descendantsTrace (.run combined children)) (childrenTrace children)
  | children_walk {identity records values before results after}
      (actual : Walk budget (.live identity records) 0 values before results after) :
      Direct (childrenTrace (.live actual)) (walkTrace actual)
  | walk_head {combined index value values before result middle results after}
      (head : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle)
      (tail : Walk budget combined (index + 1) values middle results after) :
      Direct (walkTrace (.cons head tail)) (nodeCallTrace head)
  | walk_tail {combined index value values before result middle results after}
      (head : NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle)
      (tail : Walk budget combined (index + 1) values middle results after) :
      Direct (walkTrace (.cons head tail)) (walkTrace tail)

/-- A reached graph is the root itself or follows finitely many direct constructor paths. -/
inductive Reach : Trace width budget → Trace width budget → Prop where
  | refl (trace) : Reach trace trace
  | step {before middle after} (first : Direct before middle) (rest : Reach middle after) : Reach before after

/-- A direct child is reached in one step. -/
theorem Reach.direct {before after : Trace width budget} (direct : Direct before after) : Reach before after :=
  .step direct (.refl after)

/-- Actual reached prefixes compose without any future-state predicate. -/
theorem Reach.trans {before middle after : Trace width budget} (first : Reach before middle) (rest : Reach middle after) :
    Reach before after := by
  induction first with
  | refl => exact rest
  | step first next ih => exact .step first (ih rest)

/-- Only reached actual edge bodies require the existing live-load Scan range plan. -/
def Checks (top : Trace width budget) : Prop :=
  ∀ request before result after (actual : EdgeBody budget request before result after),
    Reach top (edgeBodyTrace actual) → SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before

/-- Restrict a range plan along an actual reached prefix. -/
theorem Checks.reached {top child : Trace width budget} (checks : Checks top) (reached : Reach top child) : Checks child :=
  fun request before result after actual below => checks request before result after actual (reached.trans below)

/-- Restrict a range plan to one actual constructor child. -/
theorem Checks.restrict {top child : Trace width budget} (checks : Checks top) (direct : Direct top child) : Checks child :=
  checks.reached (Reach.direct direct)

/-- An actual edge-body leaf reads only its own request and initial physical state. -/
theorem Checks.edge_body {request result} {before after : Caller width} {actual : EdgeBody budget request before result after}
    (checks : Checks (edgeBodyTrace actual)) : SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before :=
  checks request before result after actual (.refl _)

/-- Any reached edge body supplies its exact live-load range plan. -/
theorem Checks.edge_reached {top : Trace width budget} {request result} {before after : Caller width}
    {actual : EdgeBody budget request before result after} (checks : Checks top) (reached : Reach top (edgeBodyTrace actual)) :
    SourceCurrentAllocatedPartialEdgeActual.Ranges budget request before :=
  (checks.reached reached).edge_body

/-- The reached evaluating owner supplies the old call-level range interface. -/
theorem Checks.edge_call_ranges {request result} {before after : Caller width} (actual : EdgeCall budget request before result after)
    (checks : Checks (edgeCallTrace actual)) : SourceCurrentAllocatedPartialEdgeActual.CallRanges budget request before := by
  cases actual with
  | hit actualStarted =>
      intro handle original running started
      rw [actualStarted] at started
      cases started
  | evaluate actualStarted body =>
      intro handle original running started
      have same := actualStarted.symm.trans started
      have actions := congrArg (fun result => result.2.1) same
      have states := congrArg (fun result => result.2.2) same
      cases states
      cases actions
      exact (checks.restrict (.edge_evaluate actualStarted body)).edge_body

end MicroCFTA.SourceCurrentAllocatedPartialChecks
