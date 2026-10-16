import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall

/-!
# Reached entries for constrained finite ordinary recursion

Each entry records the current control and its complete caller state.
A step enters the next control before that control completes.
Only steps past an earlier call contain its completed graph.
The range plan checks every reached parent entry at its actual state.
It does not assert completion, semantic results, or machine capacity.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Entries contain inputs and current states, without a result or completion receipt. -/
inductive Entry (width : Nat) where
  | nodeCall (request : NodeRequest) (before : Caller width)
  | nodeBody (request : NodeRequest) (before : Caller width)
  | edgeCall (request : EdgeRequest) (before : Caller width)
  | edgeBody (request : EdgeRequest) (before : Caller width)
  | rows (inherited : EqValue) (edges : List Edge) (before : Caller width)
  | descendants (inherited : EqValue) (edge : Edge) (before : Caller width)
  | children (combined : EqValue) (values : List Node) (before : Caller width)
  | walk (combined : EqValue) (index : Nat) (values : List Node) (before : Caller width)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- Each transition follows literal control order and only completed earlier prefixes. -/
inductive Step (budget : Nat) : Entry width → Entry width → Prop where
  | node_evaluate
      (started : beginNode request before = (handle, .evaluate owner, running)) :
      Step budget (.nodeCall request before) (.nodeBody owner running)
  | node_ordinary :
      Step budget (.nodeBody ⟨inherited, .node entry edges depth free⟩ before)
        (.rows inherited edges before)
  | edge_evaluate
      (started : beginEdge request before = (handle, .evaluate owner, running)) :
      Step budget (.edgeCall request before) (.edgeBody owner running)
  | rows_edge :
      Step budget (.rows inherited (original :: originals) before)
        (.edgeCall ⟨inherited, original⟩ before)
  | rows_descendants
      (earlier : EdgeCall budget ⟨inherited, original⟩ before narrowed middle) :
      Step budget (.rows inherited (original :: originals) before)
        (.descendants inherited narrowed middle)
  | rows_tail
      (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : Descendants budget inherited narrowed middle result afterChildren) :
      Step budget (.rows inherited (original :: originals) before)
        (.rows inherited originals afterChildren)
  | descendants_children
      (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
        before.checked.operations).1 = .ok (some payload)) :
      Step budget (.descendants inherited edge before)
        (.children payload edge.children (prefixState before edge inherited))
  | children_live :
      Step budget (.children (.live identity records) values before)
        (.walk (.live identity records) 0 values before)
  | walk_node :
      Step budget (.walk combined index (value :: values) before)
        (.nodeCall ⟨(descend before combined index).1, value⟩
          (descend before combined index).2)
  | walk_tail
      (earlier : NodeCall budget ⟨(descend before combined index).1, value⟩
        (descend before combined index).2 result middle) :
      Step budget (.walk combined index (value :: values) before)
        (.walk combined (index + 1) values middle)

/-- Reached entries include the root and finite chains of entry transitions. -/
inductive Reach (budget : Nat) : Entry width → Entry width → Prop where
  | refl : Reach budget entry entry
  | direct (step : Step budget first last) : Reach budget first last
  | trans (first : Reach budget start middle) (rest : Reach budget middle last) :
      Reach budget start last

/-- A plan supplies only the machine checks at each independently reached parent entry. -/
def Plan (budget : Nat) (root : Entry width) : Prop :=
  ∀ request before, Reach budget root (.edgeBody request before) →
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before

/-- Any reached control inherits the same root plan. -/
theorem Plan.restrict {budget : Nat} {root entry : Entry width}
    (plan : Plan budget root) (reached : Reach budget root entry) : Plan budget entry := by
  intro request before later
  exact plan request before (.trans reached later)

/-- The current parent entry uses its own reached machine checks. -/
theorem Plan.edge_body_ranges {budget : Nat} {request : EdgeRequest} {before : Caller width}
    (plan : Plan budget (.edgeBody request before)) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before :=
  plan request before .refl

/-- An actual evaluating observation reaches the captured owner's parent checks. -/
theorem Plan.edge_call_ranges {budget : Nat} {request : EdgeRequest} {before : Caller width}
    (plan : Plan budget (.edgeCall request before)) :
    SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.Ranges budget request before := by
  intro handle owner running started
  exact plan owner running (.direct (.edge_evaluate started))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries
