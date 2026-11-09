import MicroCFTA.SourceCurrentAllocatedSharedPartialWorker
import MicroCFTA.SourceCurrentAllocatedSharedPartialFrames

/-!
# Graphs from successful literal shared outer returns

The proof follows each actual successful observation. It retains every
intermediate caller, stored owner, inherited prefix and parent return.
The outer fuel supplies the induction. No readiness, ranges, future graph
or recursive completion certificate is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph
open Language InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialGraph
open SourceCurrentAllocatedSharedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable {width : Nat}

private theorem bind_done {A B : Type} {first : Outcome A width}
    {next : A → Caller width → Outcome B width} {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value, middle, rfl, actual⟩
  | failed fault middle => cases actual

variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A successful body retains the literal shared parent call and all nine lower bounds. -/
theorem edgeBody_graph {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    EdgeBody budget request before result after := by
  obtain ⟨checked, fourth, memo, parent, rfl⟩ := edgeBody_done actual
  exact .parent g s r e p h m c n parent

/-- An edge hit or successful stored body produces the same owner and finish graph. -/
theorem edgeCall_graph {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    EdgeCall budget request before result after := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [edgeCall, started] at actual
      cases actual
      exact .hit started
  | evaluate original =>
      simp only [edgeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      exact .evaluate started (edgeBody_graph first)
  | busy | absent => simp only [edgeCall, started] at actual; cases actual

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node},
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
      NodeCall budget request before result after

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node},
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
      NodeBody budget request before result after

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values result : List Edge}
    {before after : Caller width},
    rows fuel g s r e p h m c n budget inherited values before = .done result after →
      Rows budget inherited values before result after

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge}
    {before after : Caller width},
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
      Descendants budget inherited value before result after

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values result : List Node}
    {before after : Caller width},
    children fuel g s r e p h m c n budget combined values before = .done result after →
      Children budget combined values before result after

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values result : List Node}
    {before after : Caller width},
    walk fuel g s r e p h m c n budget combined index values before = .done result after →
      Walk budget combined index values before result after

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt (width := width) fuel) :
    NodeCallAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result actual
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [nodeCall, started] at actual
      cases actual
      exact .hit started
  | evaluate original =>
      simp only [nodeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      exact .evaluate started (body first)
  | busy | absent => simp only [nodeCall, started] at actual; cases actual

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt (width := width) smaller) :
    WalkAt (width := width) fuel := by
  intro g s r e p h m c n budget combined index values result before after actual
  cases values with
  | nil =>
      simp only [walk] at actual
      cases actual
      exact .nil
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
          simp only [walk] at actual
          obtain ⟨headValue, middle, first, remaining⟩ := bind_done actual
          obtain ⟨restValues, finalState, tail, last⟩ := bind_done remaining
          cases last
          exact .cons (nodes fuel (Nat.lt_succ_self _) first) (tails fuel (Nat.lt_succ_self _) tail)

private theorem children_step (fuel : Nat) (walks : WalkAt (width := width) fuel) :
    ChildrenAt (width := width) fuel := by
  intro g s r e p h m c n budget combined values result before after actual
  cases combined with
  | contradiction =>
      simp only [children] at actual
      cases actual
      exact .contradiction
  | live identity records =>
      simp only [children] at actual
      exact .live (walks actual)

private theorem descendants_step (fuel : Nat) (child : ChildrenAt (width := width) fuel) :
    DescendantsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited value result before after actual
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants, observed] at actual; cases actual
      | ok answer =>
          cases answer with
          | none => simp only [descendants, observed] at actual; cases actual
          | some combined =>
              have prefixSame : prefixState before value inherited =
                  advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                    ⟨before.checked.native.machine.heap, operations⟩) before.fourth before.merge := by
                simp only [prefixState, SourceCurrentAllocatedInheritedPrefix.state, observed]
              simp only [descendants, observed] at actual
              rw [← prefixSame] at actual
              obtain ⟨values, middle, first, last⟩ := bind_done actual
              cases last
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              exact .run combinedEquation (child first)

private theorem rows_step (fuel : Nat)
    (descend : ∀ smaller, smaller < fuel → DescendantsAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    RowsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited values result before after actual
  cases values with
  | nil =>
      simp only [rows] at actual
      cases actual
      exact .nil
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at actual; cases actual
      | succ fuel =>
          simp only [rows] at actual
          obtain ⟨narrowed, middle, first, remaining⟩ := bind_done actual
          obtain ⟨edgeResult, current, second, remaining⟩ := bind_done remaining
          obtain ⟨restResults, finalState, tail, last⟩ := bind_done remaining
          cases last
          exact .cons (edgeCall_graph first) (descend fuel (Nat.lt_succ_self _) second)
            (tails fuel (Nat.lt_succ_self _) tail)

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    NodeBodyAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result actual
  cases request with
  | mk inherited value =>
      cases value with
      | empty =>
          simp only [nodeBody] at actual
          cases actual
          exact .empty
      | union entry members depth free =>
          simp only [nodeBody] at actual
          cases actual
          exact .union
      | reference name => simp only [nodeBody] at actual; cases actual
      | mu entry body depth ordinary =>
          cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
          | pending => simp only [nodeBody, observed] at actual; cases actual
          | done value heap =>
              simp only [nodeBody, observed] at actual
              cases actual
              exact .binder observed
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
              simp only [nodeBody] at actual
              obtain ⟨results, middle, first, last⟩ := bind_done actual
              cases last
              exact .ordinary (rowCalls fuel (Nat.lt_succ_self _) first)

private theorem all_graphs (fuel : Nat) :
    NodeCallAt (width := width) fuel ∧ NodeBodyAt (width := width) fuel ∧
    RowsAt (width := width) fuel ∧ DescendantsAt (width := width) fuel ∧
    ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks : WalkAt (width := width) fuel :=
        walk_step fuel (fun smaller less => (ih smaller less).1)
          (fun smaller less => (ih smaller less).2.2.2.2.2)
      have children : ChildrenAt (width := width) fuel := children_step fuel walks
      have descendants : DescendantsAt (width := width) fuel := descendants_step fuel children
      have rows : RowsAt (width := width) fuel :=
        rows_step fuel (fun smaller less => (ih smaller less).2.2.2.1)
          (fun smaller less => (ih smaller less).2.2.1)
      have body : NodeBodyAt (width := width) fuel :=
        nodeBody_step fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step fuel body, body, rows, descendants, children, walks⟩

/-- Every successful node call has its actual shared owner graph. -/
theorem nodeCall_graph {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    NodeCall budget request before result after := (all_graphs fuel).1 actual

/-- Every successful node body retains its literal terminal, binder or ordinary branch. -/
theorem nodeBody_graph {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node}
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done result after) :
    NodeBody budget request before result after := (all_graphs fuel).2.1 actual

/-- Every successful row traversal retains edge calls, returned descendants and suffix order. -/
theorem rows_graph {fuel g s r e p h m c n budget : Nat} {inherited : EqValue}
    {values result : List Edge} {before after : Caller width}
    (actual : rows fuel g s r e p h m c n budget inherited values before = .done result after) :
    Rows budget inherited values before result after := (all_graphs fuel).2.2.1 actual

/-- Every successful descendant traversal retains the actual inherited prefix and rebuild. -/
theorem descendants_graph {fuel g s r e p h m c n budget : Nat} {inherited : EqValue}
    {value result : Edge} {before after : Caller width}
    (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after) :
    Descendants budget inherited value before result after := (all_graphs fuel).2.2.2.1 actual

/-- Every successful child traversal retains contradiction erasure or its literal indexed walk. -/
theorem children_graph {fuel g s r e p h m c n budget : Nat} {combined : EqValue}
    {values result : List Node} {before after : Caller width}
    (actual : children fuel g s r e p h m c n budget combined values before = .done result after) :
    Children budget combined values before result after := (all_graphs fuel).2.2.2.2.1 actual

/-- Every successful walk retains each current descended request and exact returned caller. -/
theorem walk_graph {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat}
    {values result : List Node} {before after : Caller width}
    (actual : walk fuel g s r e p h m c n budget combined index values before = .done result after) :
    Walk budget combined index values before result after := (all_graphs fuel).2.2.2.2.2 actual

/-- The actual successful nodeCall return preserves both families' protected cells. -/
theorem nodeCall_frame {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.node_call (nodeCall_graph actual) valid

/-- The actual successful nodeBody return preserves both families' protected cells. -/
theorem nodeBody_frame {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node}
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.node_body (nodeBody_graph actual) valid

/-- The actual successful edgeCall return preserves both families' protected cells. -/
theorem edgeCall_frame {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.edge_call (edgeCall_graph actual) valid

/-- The actual successful edgeBody return preserves both families' protected cells. -/
theorem edgeBody_frame {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.edge_body (edgeBody_graph actual) valid

/-- The actual successful rows return preserves both families' protected cells. -/
theorem rows_frame {fuel g s r e p h m c n budget : Nat} {inherited : EqValue}
    {values result : List Edge} {before after : Caller width}
    (actual : rows fuel g s r e p h m c n budget inherited values before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.rows (rows_graph actual) valid

/-- The actual successful descendants return preserves both families' protected cells. -/
theorem descendants_frame {fuel g s r e p h m c n budget : Nat} {inherited : EqValue}
    {value result : Edge} {before after : Caller width}
    (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.descendants (descendants_graph actual) valid

/-- The actual successful children return preserves both families' protected cells. -/
theorem children_frame {fuel g s r e p h m c n budget : Nat} {combined : EqValue}
    {values result : List Node} {before after : Caller width}
    (actual : children fuel g s r e p h m c n budget combined values before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.children (children_graph actual) valid

/-- The actual successful walk return preserves both families' protected cells. -/
theorem walk_frame {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat}
    {values result : List Node} {before after : Caller width}
    (actual : walk fuel g s r e p h m c n budget combined index values before = .done result after)
    (valid : SourceCurrentAllocatedSharedPartialFrames.Protocol before) :
    SourceCurrentAllocatedSharedPartialFrames.Frame before after :=
  SourceCurrentAllocatedSharedPartialFrames.walk (walk_graph actual) valid

end MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph
