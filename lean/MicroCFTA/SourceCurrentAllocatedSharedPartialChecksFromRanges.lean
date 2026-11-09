import MicroCFTA.SourceCurrentAllocatedSharedPartialChecksComposition
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph

/-!
# Graph checks from literal shared execution ranges

The actual outer fuel selects each successful execution prefix. Its literal
range predicate supplies the reached Parent check before any outcome.
Constructor composition identifies alternative completed child states by
shared execution determinism. The proof identifies graph certificates only
after their physical indices agree. No Context, capacity or future range supplier is
added. This proof does not reindex canonical endpoint reads.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialChecksFromRanges
open Language InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedSharedPartialGraph
open SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentAllocatedSharedPartialChecks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "RNode" => SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
local notation "RBody" => SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody
local notation "REdge" => SourceCurrentAllocatedSharedPartialWorkerRanges.edgeCall
local notation "REdgeBody" => SourceCurrentAllocatedSharedPartialWorkerRanges.edgeBody
local notation "RRows" => SourceCurrentAllocatedSharedPartialWorkerRanges.rows
local notation "RDescendants" => SourceCurrentAllocatedSharedPartialWorkerRanges.descendants
local notation "RChildren" => SourceCurrentAllocatedSharedPartialWorkerRanges.children
local notation "RWalk" => SourceCurrentAllocatedSharedPartialWorkerRanges.walk
variable {width : Nat}

private theorem bind_done {A B : Type} {first : Outcome A width}
    {next : A → Caller width → Outcome B width} {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value, middle, rfl, actual⟩
  | failed fault middle => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A shared Parent leaf retains its range plan at the same input indices. -/
theorem edge_body {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (ranges : REdgeBody fuel g s r e p h m c n budget request before)
    (graph : EdgeBody budget request before result after) : Checks (edgeBodyTrace graph) :=
  SourceCurrentAllocatedSharedPartialChecksComposition.edge_body graph ranges

/-- A successful edge uses the literal captured owner's check. -/
theorem edge_call {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (ranges : REdge fuel g s r e p h m c n budget request before)
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (graph : EdgeCall budget request before result after) : Checks (edgeCallTrace graph) := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [edgeCall, started] at actual
      cases actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.edge_hit started
  | evaluate original =>
      have bodyRanges := SourceCurrentAllocatedSharedPartialWorkerRanges.edgeCall_of_evaluate ranges started
      simp only [edgeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      have body := SourceCurrentAllocatedSharedPartialWorkerGraph.edgeBody_graph first
      exact SourceCurrentAllocatedSharedPartialChecksComposition.edge_evaluate started body (edge_body bodyRanges body)
  | busy | absent => simp only [edgeCall, started] at actual; cases actual

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node},
    RNode fuel g s r e p h m c n budget request before →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    ∀ graph : NodeCall budget request before result after, Checks (nodeCallTrace graph)

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node},
    RBody fuel g s r e p h m c n budget request before →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    ∀ graph : NodeBody budget request before result after, Checks (nodeBodyTrace graph)

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values result : List Edge} {before after : Caller width},
    RRows fuel g s r e p h m c n budget inherited values before →
    rows fuel g s r e p h m c n budget inherited values before = .done result after →
    ∀ graph : Rows budget inherited values before result after, Checks (rowsTrace graph)

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller width},
    RDescendants fuel g s r e p h m c n budget inherited value before →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    ∀ graph : Descendants budget inherited value before result after, Checks (descendantsTrace graph)

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values result : List Node} {before after : Caller width},
    RChildren fuel g s r e p h m c n budget combined values before →
    children fuel g s r e p h m c n budget combined values before = .done result after →
    ∀ graph : Children budget combined values before result after, Checks (childrenTrace graph)

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values result : List Node} {before after : Caller width},
    RWalk fuel g s r e p h m c n budget combined index values before →
    walk fuel g s r e p h m c n budget combined index values before = .done result after →
    ∀ graph : Walk budget combined index values before result after, Checks (walkTrace graph)

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt (width := width) fuel) :
    NodeCallAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result ranges actual graph
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value =>
      simp only [nodeCall, started] at actual
      cases actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.node_hit started
  | evaluate original =>
      have bodyRanges := SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall_of_evaluate ranges started
      simp only [nodeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      have bodyGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeBody_graph first
      exact SourceCurrentAllocatedSharedPartialChecksComposition.node_evaluate started bodyGraph
        (body bodyRanges first bodyGraph)
  | busy | absent => simp only [nodeCall, started] at actual; cases actual

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt (width := width) smaller) :
    WalkAt (width := width) fuel := by
  intro g s r e p h m c n budget combined index values result before after ranges actual graph
  cases values with
  | nil =>
      simp only [walk] at actual
      cases actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.walk_nil
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
          simp only [walk] at actual
          simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.walk] at ranges
          obtain ⟨headValue, middle, first, remaining⟩ := bind_done actual
          obtain ⟨restValues, finalState, tail, last⟩ := bind_done remaining
          cases last
          have headGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeCall_graph first
          have tailGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.walk_graph tail
          have tailRanges := SourceCurrentAllocatedSharedPartialWorkerRanges.after_of_done ranges.2 first
          exact SourceCurrentAllocatedSharedPartialChecksComposition.walk_cons headGraph tailGraph
            (nodes fuel (Nat.lt_succ_self _) ranges.1 first headGraph)
            (tails fuel (Nat.lt_succ_self _) tailRanges tail tailGraph)

private theorem children_step (fuel : Nat) (walks : WalkAt (width := width) fuel) :
    ChildrenAt (width := width) fuel := by
  intro g s r e p h m c n budget combined values result before after ranges actual graph
  cases combined with
  | contradiction =>
      simp only [children] at actual
      cases actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.children_contradiction
  | live identity records =>
      simp only [children] at actual
      simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.children] at ranges
      have walkGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.walk_graph actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.children_live walkGraph (walks ranges actual walkGraph)

private theorem descendants_step (fuel : Nat) (child : ChildrenAt (width := width) fuel) :
    DescendantsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited value result before after ranges actual graph
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
              have childRanges : RChildren fuel g s r e p h m c n budget combined value.children
                  (prefixState before value inherited) := by
                simpa only [SourceCurrentAllocatedSharedPartialWorkerRanges.descendants, observed] using ranges
              simp only [descendants, observed] at actual
              rw [← prefixSame] at actual
              obtain ⟨values, middle, first, last⟩ := bind_done actual
              cases last
              have combinedEquation : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited
                  before.checked.operations).1 = .ok (some combined) := by rw [observed]
              have childGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.children_graph first
              exact SourceCurrentAllocatedSharedPartialChecksComposition.descendants_run combinedEquation childGraph
                (child childRanges first childGraph)

private theorem rows_step (fuel : Nat)
    (descend : ∀ smaller, smaller < fuel → DescendantsAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    RowsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited values result before after ranges actual graph
  cases values with
  | nil =>
      simp only [rows] at actual
      cases actual
      exact SourceCurrentAllocatedSharedPartialChecksComposition.rows_nil
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at actual; cases actual
      | succ fuel =>
          simp only [rows] at actual
          simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.rows] at ranges
          obtain ⟨narrowed, middle, first, remaining⟩ := bind_done actual
          obtain ⟨edgeResult, current, second, remaining⟩ := bind_done remaining
          obtain ⟨restResults, finalState, tail, last⟩ := bind_done remaining
          cases last
          have edgeGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.edgeCall_graph first
          have childGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.descendants_graph second
          have tailGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.rows_graph tail
          have descendantRanges := SourceCurrentAllocatedSharedPartialWorkerRanges.after_of_done ranges.2 first
          have tailRanges := SourceCurrentAllocatedSharedPartialWorkerRanges.after_of_done descendantRanges.2 second
          exact SourceCurrentAllocatedSharedPartialChecksComposition.rows_cons edgeGraph childGraph tailGraph
            (edge_call ranges.1 first edgeGraph)
            (descend fuel (Nat.lt_succ_self _) descendantRanges.1 second childGraph)
            (tails fuel (Nat.lt_succ_self _) tailRanges tail tailGraph)

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    NodeBodyAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result ranges actual graph
  cases request with
  | mk inherited value =>
      cases value with
      | empty =>
          simp only [nodeBody] at actual
          cases actual
          exact SourceCurrentAllocatedSharedPartialChecksComposition.empty
      | union entry members depth free =>
          simp only [nodeBody] at actual
          cases actual
          exact SourceCurrentAllocatedSharedPartialChecksComposition.union
      | reference name => simp only [nodeBody] at actual; cases actual
      | mu entry body depth ordinary =>
          cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
          | pending => simp only [nodeBody, observed] at actual; cases actual
          | done value heap =>
              simp only [nodeBody, observed] at actual
              cases actual
              exact SourceCurrentAllocatedSharedPartialChecksComposition.binder observed
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
              simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody] at ranges
              have rowRanges : RRows fuel g s r e p h m c n budget inherited original before := ranges
              simp only [nodeBody] at actual
              obtain ⟨results, middle, first, last⟩ := bind_done actual
              cases last
              have rowGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.rows_graph first
              exact SourceCurrentAllocatedSharedPartialChecksComposition.ordinary rowGraph
                (rowCalls fuel (Nat.lt_succ_self _) rowRanges first rowGraph)

private theorem all_checks (fuel : Nat) :
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

/-- Literal nodeCall ranges derive checks for the given graph at exactly the same physical indices. -/
theorem node_call {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (ranges : RNode fuel g s r e p h m c n budget request before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (graph : NodeCall budget request before result after) : Checks (nodeCallTrace graph) :=
  (all_checks fuel).1 ranges actual graph

/-- Literal nodeBody ranges derive checks for the given graph at exactly the same physical indices. -/
theorem node_body {fuel g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (ranges : RBody fuel g s r e p h m c n budget request before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.nodeBody fuel g s r e p h m c n budget request before = .done result after)
    (graph : NodeBody budget request before result after) : Checks (nodeBodyTrace graph) :=
  (all_checks fuel).2.1 ranges actual graph

/-- Literal rows ranges derive checks for the given graph at exactly the same physical indices. -/
theorem rows {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {values result : List Edge} {before after : Caller width}
    (ranges : RRows fuel g s r e p h m c n budget inherited values before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.rows fuel g s r e p h m c n budget inherited values before = .done result after)
    (graph : Rows budget inherited values before result after) : Checks (rowsTrace graph) :=
  (all_checks fuel).2.2.1 ranges actual graph

/-- Literal descendants ranges derive checks for the given graph at exactly the same physical indices. -/
theorem descendants {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (ranges : RDescendants fuel g s r e p h m c n budget inherited value before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before = .done result after)
    (graph : Descendants budget inherited value before result after) : Checks (descendantsTrace graph) :=
  (all_checks fuel).2.2.2.1 ranges actual graph

/-- Literal children ranges derive checks for the given graph at exactly the same physical indices. -/
theorem children {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {values result : List Node} {before after : Caller width}
    (ranges : RChildren fuel g s r e p h m c n budget combined values before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done result after)
    (graph : Children budget combined values before result after) : Checks (childrenTrace graph) :=
  (all_checks fuel).2.2.2.2.1 ranges actual graph

/-- Literal walk ranges derive checks for the given graph at exactly the same physical indices. -/
theorem walk {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values result : List Node} {before after : Caller width}
    (ranges : RWalk fuel g s r e p h m c n budget combined index values before)
    (actual : SourceCurrentAllocatedSharedPartialWorker.walk fuel g s r e p h m c n budget combined index values before = .done result after)
    (graph : Walk budget combined index values before result after) : Checks (walkTrace graph) :=
  (all_checks fuel).2.2.2.2.2 ranges actual graph

end MicroCFTA.SourceCurrentAllocatedSharedPartialChecksFromRanges
