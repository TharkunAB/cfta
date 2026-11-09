import MicroCFTA.SourceCurrentAllocatedSharedPartialChecks
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerRanges
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorkerGraph

/-!
# Literal shared execution ranges from completed graph checks

Each supplied successful run selects its exact intermediate callers. The
proof constructs child graphs from those literal observations and restricts
the given checks along their direct paths. Root graph proofs have equal
physical indices before proof irrelevance identifies them.

The result applies at the supplied bounds. It does not require a larger
forecast Room, identify ordered reads, or cover failed runs.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedPartialRangesFromChecks
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

/-- A checked shared Parent leaf supplies its current range plan at every literal bound. -/
theorem edge_body {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge} {graph : EdgeBody budget request before result after}
    (checks : Checks (edgeBodyTrace graph))
    (_actual : edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    REdgeBody fuel g s r e p h m c n budget request before := checks.edge_body

/-- A successful edge checks the same captured owner and actual body entry. -/
theorem edge_call {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge} {graph : EdgeCall budget request before result after}
    (checks : Checks (edgeCallTrace graph))
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    REdge fuel g s r e p h m c n budget request before := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready value => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.edgeCall, started]
  | evaluate original =>
      simp only [edgeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      have bodyGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.edgeBody_graph first
      have bodyChecks : Checks (edgeBodyTrace bodyGraph) :=
        checks.restrict (.edge_evaluate started bodyGraph)
      have bodyRanges := edge_body bodyChecks first
      simpa only [SourceCurrentAllocatedSharedPartialWorkerRanges.edgeCall, started] using bodyRanges
  | busy | absent => simp only [edgeCall, started] at actual; cases actual

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {graph : NodeCall budget request before result after},
    Checks (nodeCallTrace graph) →
    nodeCall fuel g s r e p h m c n budget request before = .done result after →
    RNode fuel g s r e p h m c n budget request before

private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    {graph : NodeBody budget request before result after},
    Checks (nodeBodyTrace graph) →
    nodeBody fuel g s r e p h m c n budget request before = .done result after →
    RBody fuel g s r e p h m c n budget request before

private def RowsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {values result : List Edge} {before after : Caller width}
    {graph : Rows budget inherited values before result after},
    Checks (rowsTrace graph) →
    rows fuel g s r e p h m c n budget inherited values before = .done result after →
    RRows fuel g s r e p h m c n budget inherited values before

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {graph : Descendants budget inherited value before result after},
    Checks (descendantsTrace graph) →
    descendants fuel g s r e p h m c n budget inherited value before = .done result after →
    RDescendants fuel g s r e p h m c n budget inherited value before

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {values result : List Node} {before after : Caller width}
    {graph : Children budget combined values before result after},
    Checks (childrenTrace graph) →
    children fuel g s r e p h m c n budget combined values before = .done result after →
    RChildren fuel g s r e p h m c n budget combined values before

private def WalkAt (fuel : Nat) : Prop :=
  ∀ {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values result : List Node} {before after : Caller width}
    {graph : Walk budget combined index values before result after},
    Checks (walkTrace graph) →
    walk fuel g s r e p h m c n budget combined index values before = .done result after →
    RWalk fuel g s r e p h m c n budget combined index values before

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt (width := width) fuel) :
    NodeCallAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result graph checks actual
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall, started]
  | evaluate original =>
      simp only [nodeCall, started] at actual
      obtain ⟨value, middle, first, last⟩ := bind_done actual
      cases last
      have bodyGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeBody_graph first
      have bodyChecks : Checks (nodeBodyTrace bodyGraph) :=
        checks.restrict (.node_evaluate started bodyGraph)
      have bodyRanges := body bodyChecks first
      simpa only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall, started] using bodyRanges
  | busy | absent => simp only [nodeCall, started] at actual; cases actual

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt (width := width) smaller) :
    WalkAt (width := width) fuel := by
  intro g s r e p h m c n budget combined index values result before after graph checks actual
  cases values with
  | nil => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.walk]
  | cons value rest =>
      cases fuel with
      | zero => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.walk]
      | succ fuel =>
          simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.walk]
          simp only [walk] at actual
          obtain ⟨headValue, middle, first, remaining⟩ := bind_done actual
          obtain ⟨restValues, finalState, tail, last⟩ := bind_done remaining
          cases last
          have headGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.nodeCall_graph first
          have tailGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.walk_graph tail
          have headChecks : Checks (nodeCallTrace headGraph) :=
            checks.restrict (.walk_head headGraph tailGraph)
          have tailChecks : Checks (walkTrace tailGraph) :=
            checks.restrict (.walk_tail headGraph tailGraph)
          refine ⟨nodes fuel (Nat.lt_succ_self _) headChecks first, ?_⟩
          have tailRanges := tails fuel (Nat.lt_succ_self _) tailChecks tail
          simpa only [first, SourceCurrentAllocatedSharedPartialWorkerRanges.After] using tailRanges

private theorem children_step (fuel : Nat) (walks : WalkAt (width := width) fuel) :
    ChildrenAt (width := width) fuel := by
  intro g s r e p h m c n budget combined values result before after graph checks actual
  cases combined with
  | contradiction => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.children]
  | live identity records =>
      simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.children]
      simp only [children] at actual
      have walkGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.walk_graph actual
      have walkChecks : Checks (walkTrace walkGraph) := checks.restrict (.children_walk walkGraph)
      exact walks walkChecks actual

private theorem descendants_step (fuel : Nat) (child : ChildrenAt (width := width) fuel) :
    DescendantsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited value result before after graph checks actual
  cases observed : SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.descendants, observed]
      | ok answer =>
          cases answer with
          | none => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.descendants, observed]
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
              have childGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.children_graph first
              have childChecks : Checks (childrenTrace childGraph) :=
                checks.restrict (.descendants_children combinedEquation childGraph)
              have childRanges := child childChecks first
              simpa only [SourceCurrentAllocatedSharedPartialWorkerRanges.descendants, observed] using childRanges

private theorem rows_step (fuel : Nat)
    (descend : ∀ smaller, smaller < fuel → DescendantsAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    RowsAt (width := width) fuel := by
  intro g s r e p h m c n budget inherited values result before after graph checks actual
  cases values with
  | nil => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.rows]
  | cons original rest =>
      cases fuel with
      | zero => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.rows]
      | succ fuel =>
          simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.rows]
          simp only [rows] at actual
          obtain ⟨narrowed, middle, first, remaining⟩ := bind_done actual
          obtain ⟨edgeResult, current, second, remaining⟩ := bind_done remaining
          obtain ⟨restResults, finalState, tail, last⟩ := bind_done remaining
          cases last
          have edgeGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.edgeCall_graph first
          have childGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.descendants_graph second
          have tailGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.rows_graph tail
          have edgeChecks : Checks (edgeCallTrace edgeGraph) :=
            checks.restrict (.rows_edge edgeGraph childGraph tailGraph)
          have childChecks : Checks (descendantsTrace childGraph) :=
            checks.restrict (.rows_descendants edgeGraph childGraph tailGraph)
          have tailChecks : Checks (rowsTrace tailGraph) :=
            checks.restrict (.rows_tail edgeGraph childGraph tailGraph)
          refine ⟨edge_call edgeChecks first, ?_⟩
          have childRanges := descend fuel (Nat.lt_succ_self _) childChecks second
          have tailRanges := tails fuel (Nat.lt_succ_self _) tailChecks tail
          simpa only [first, second, SourceCurrentAllocatedSharedPartialWorkerRanges.After] using
            And.intro childRanges tailRanges

private theorem nodeBody_step (fuel : Nat)
    (rowCalls : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) :
    NodeBodyAt (width := width) fuel := by
  intro g s r e p h m c n budget request before after result graph checks actual
  cases request with
  | mk inherited value =>
      cases value with
      | empty => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
      | union entry members depth free => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
      | reference name => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
      | mu entry body depth ordinary => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
          | succ fuel =>
              simp only [SourceCurrentAllocatedSharedPartialWorkerRanges.nodeBody]
              simp only [nodeBody] at actual
              obtain ⟨results, middle, first, last⟩ := bind_done actual
              cases last
              have rowGraph := SourceCurrentAllocatedSharedPartialWorkerGraph.rows_graph first
              have rowChecks : Checks (rowsTrace rowGraph) := checks.restrict (.node_ordinary rowGraph)
              exact rowCalls fuel (Nat.lt_succ_self _) rowChecks first

private theorem all_ranges (fuel : Nat) :
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

/-- Given node-call checks apply to the same successful run at its actual bounds. -/
theorem node_call {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node} {graph : NodeCall budget request before result after}
    (checks : Checks (nodeCallTrace graph))
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    RNode fuel g s r e p h m c n budget request before := (all_ranges fuel).1 checks actual

/-- Given node-body checks apply to the literal successful reconstruction branch. -/
theorem node_body {fuel g s r e p h m c n budget : Nat} {request : NodeRequest}
    {before after : Caller width} {result : Node} {graph : NodeBody budget request before result after}
    (checks : Checks (nodeBodyTrace graph))
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done result after) :
    RBody fuel g s r e p h m c n budget request before := (all_ranges fuel).2.1 checks actual

/-- Given row checks apply to the actual edge, descendants and suffix sequence. -/
theorem rows {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {values result : List Edge}
    {before after : Caller width} {graph : Rows budget inherited values before result after}
    (checks : Checks (rowsTrace graph))
    (actual : SourceCurrentAllocatedSharedPartialWorker.rows fuel g s r e p h m c n budget inherited values before = .done result after) :
    RRows fuel g s r e p h m c n budget inherited values before := (all_ranges fuel).2.2.1 checks actual

/-- Given descendant checks apply at the observed inherited-prefix caller. -/
theorem descendants {fuel g s r e p h m c n budget : Nat} {inherited : EqValue} {value result : Edge}
    {before after : Caller width} {graph : Descendants budget inherited value before result after}
    (checks : Checks (descendantsTrace graph))
    (actual : SourceCurrentAllocatedSharedPartialWorker.descendants fuel g s r e p h m c n budget inherited value before = .done result after) :
    RDescendants fuel g s r e p h m c n budget inherited value before := (all_ranges fuel).2.2.2.1 checks actual

/-- Given child checks apply to contradiction erasure or the actual live walk. -/
theorem children {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {values result : List Node}
    {before after : Caller width} {graph : Children budget combined values before result after}
    (checks : Checks (childrenTrace graph))
    (actual : SourceCurrentAllocatedSharedPartialWorker.children fuel g s r e p h m c n budget combined values before = .done result after) :
    RChildren fuel g s r e p h m c n budget combined values before := (all_ranges fuel).2.2.2.2.1 checks actual

/-- Given walk checks follow each actual descended request and successful tail. -/
theorem walk {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {values result : List Node}
    {before after : Caller width} {graph : Walk budget combined index values before result after}
    (checks : Checks (walkTrace graph))
    (actual : SourceCurrentAllocatedSharedPartialWorker.walk fuel g s r e p h m c n budget combined index values before = .done result after) :
    RWalk fuel g s r e p h m c n budget combined index values before := (all_ranges fuel).2.2.2.2.2 checks actual

end MicroCFTA.SourceCurrentAllocatedSharedPartialRangesFromChecks
