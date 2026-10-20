import MicroCFTA.SourceCurrentOpenOrdinaryLeafSourceCalls

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.OpenOrdinaryLeafSourceCallsFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves slot)
open InternedEdgeResidency (nodeEdges)
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool

private def outcomeValue (actual : Outcome Nat Bool Node) : Node :=
  match actual with | .done value _ => value | .pending .. => .empty
private def leafSource : Syntax Nat Bool := .node [.mk 1 false []]
private def seedSource : Syntax Nat Bool := .node [.mk 3 true [leafSource,leafSource]]
private def seedCall := build seedSource [] (empty : Heap)
private def seed : Node := outcomeValue seedCall
private def seedHeap : Heap := seedCall.state
private def inputs : List Node := [.reference .depth]
private def expressions : List (EdgeSyntax Nat Bool) :=
  [.mk 9 false [.var 0,leafSource],.mk 3 true [leafSource,leafSource],.mk 9 false [.var 0,leafSource]]
private def rawCall := build (.node expressions) inputs seedHeap
private def raw : Node := outcomeValue rawCall
private def after : Heap := rawCall.state
private def leaf : Node := outcomeValue (build leafSource [] (empty : Heap))

private theorem seed_done : build seedSource [] empty = .done seed seedHeap := by cbv
private theorem raw_done : build (.node expressions) inputs seedHeap = .done raw after := by cbv
private theorem callback_done : callback (.node expressions) [] .depth seedHeap = .done raw after := by cbv
private theorem seed_context : Context seedHeap [] := by
  simpa only [seedCall,seed_done,Outcome.state] using
    (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).build seedSource
private theorem raw_context : Context seedHeap inputs :=
  seed_context.local .depth (InternedNestedProvenance.depth_available seedHeap)
private theorem duplicated : expressions[0]? = expressions[2]? := rfl
private theorem reordered_source : expressions[1]? = some (.mk 3 true [leafSource,leafSource]) := rfl
private theorem reordered_result : (nodeEdges raw).map (fun row => row.entry.key.symbol) = [3,9] := by cbv
private theorem opened : raw.free ≠ [] := by
  cbv
  intro impossible
  cases impossible
private theorem leaf_closed : leaf.free = [] := by cbv
private theorem first_leaf : (leaves raw)[0]? = some leaf := by cbv
private theorem repeated_leaf : (leaves raw)[1]? = some leaf := by cbv
private theorem first_slot : slot (leaves raw) leaf = 0 := by cbv
private theorem distinct_occurrence : 1 ≠ slot (leaves raw) leaf := by rw [first_slot]; decide

private def Certificate : Prop :=
  ∃ outputIndex row childIndex child inner sourceIndex symbol guard children rows middle,
    ∃ call : RowCall expressions inputs seedHeap rows middle after sourceIndex symbol guard children,
    ∃ childSyntax current next,
    (nodeEdges raw)[outputIndex]? = some row ∧ row.children[childIndex]? = some child ∧
    (leaves child)[inner]? = some leaf ∧
    1 = (edgeLeaves ((nodeEdges raw).take outputIndex)).length +
      (manyLeaves (row.children.take childIndex)).length + inner ∧
    buildEdges expressions inputs seedHeap = .done rows middle ∧
    run (makeNode rows) middle = (raw,after) ∧ call.output = row ∧
    children[childIndex]? = some childSyntax ∧ call.values[childIndex]? = some child ∧
    buildMany (children.take childIndex) inputs call.current = .done (call.values.take childIndex) current ∧
    Context current inputs ∧ build childSyntax inputs current = .done child next ∧
    buildMany (children.drop (childIndex + 1)) inputs next = .done (call.values.drop (childIndex + 1)) call.middle ∧
    sizeOf childSyntax < sizeOf (Syntax.node expressions)

private theorem certificate : Certificate := by
  unfold Certificate
  exact SourceCurrentOpenOrdinaryLeafSourceCalls.node_leaf expressions inputs seedHeap raw after
    raw_context raw_done opened 1 leaf repeated_leaf

private def Claim : Prop :=
  build seedSource [] empty = .done seed seedHeap ∧
  Context seedHeap inputs ∧
  build (.node expressions) inputs seedHeap = .done raw after ∧
  callback (.node expressions) [] .depth seedHeap = .done raw after ∧
  expressions[0]? = expressions[2]? ∧
  expressions[1]? = some (.mk 3 true [leafSource,leafSource]) ∧
  (nodeEdges raw).map (fun row => row.entry.key.symbol) = [3,9] ∧
  raw.free ≠ [] ∧ leaf.free = [] ∧
  (leaves raw)[0]? = some leaf ∧ (leaves raw)[1]? = some leaf ∧
  slot (leaves raw) leaf = 0 ∧ 1 ≠ slot (leaves raw) leaf ∧
  ∃ outputIndex row childIndex child inner sourceIndex symbol guard children rows middle,
    ∃ call : RowCall expressions inputs seedHeap rows middle after sourceIndex symbol guard children,
    ∃ childSyntax current next,
    (nodeEdges raw)[outputIndex]? = some row ∧ row.children[childIndex]? = some child ∧
    (leaves child)[inner]? = some leaf ∧
    1 = (edgeLeaves ((nodeEdges raw).take outputIndex)).length +
      (manyLeaves (row.children.take childIndex)).length + inner ∧
    buildEdges expressions inputs seedHeap = .done rows middle ∧
    run (makeNode rows) middle = (raw,after) ∧ call.output = row ∧
    children[childIndex]? = some childSyntax ∧ call.values[childIndex]? = some child ∧
    buildMany (children.take childIndex) inputs call.current = .done (call.values.take childIndex) current ∧
    Context current inputs ∧ build childSyntax inputs current = .done child next ∧
    buildMany (children.drop (childIndex + 1)) inputs next = .done (call.values.drop (childIndex + 1)) call.middle ∧
    sizeOf childSyntax < sizeOf (Syntax.node expressions)

private theorem checked_witness : Claim :=
  ⟨seed_done,raw_context,raw_done,callback_done,duplicated,reordered_source,reordered_result,
    opened,leaf_closed,first_leaf,repeated_leaf,first_slot,distinct_occurrence,certificate⟩

/-- An actual open callback retains a repeated closed leaf and its strict indexed source-child call. -/
theorem witness :
  build seedSource [] empty = .done seed seedHeap ∧
  Context seedHeap inputs ∧
  build (.node expressions) inputs seedHeap = .done raw after ∧
  callback (.node expressions) [] .depth seedHeap = .done raw after ∧
  expressions[0]? = expressions[2]? ∧
  expressions[1]? = some (.mk 3 true [leafSource,leafSource]) ∧
  (nodeEdges raw).map (fun row => row.entry.key.symbol) = [3,9] ∧
  raw.free ≠ [] ∧ leaf.free = [] ∧
  (leaves raw)[0]? = some leaf ∧ (leaves raw)[1]? = some leaf ∧
  slot (leaves raw) leaf = 0 ∧ 1 ≠ slot (leaves raw) leaf ∧
  ∃ outputIndex row childIndex child inner sourceIndex symbol guard children rows middle,
    ∃ call : RowCall expressions inputs seedHeap rows middle after sourceIndex symbol guard children,
    ∃ childSyntax current next,
    (nodeEdges raw)[outputIndex]? = some row ∧ row.children[childIndex]? = some child ∧
    (leaves child)[inner]? = some leaf ∧
    1 = (edgeLeaves ((nodeEdges raw).take outputIndex)).length +
      (manyLeaves (row.children.take childIndex)).length + inner ∧
    buildEdges expressions inputs seedHeap = .done rows middle ∧
    run (makeNode rows) middle = (raw,after) ∧ call.output = row ∧
    children[childIndex]? = some childSyntax ∧ call.values[childIndex]? = some child ∧
    buildMany (children.take childIndex) inputs call.current = .done (call.values.take childIndex) current ∧
    Context current inputs ∧ build childSyntax inputs current = .done child next ∧
    buildMany (children.drop (childIndex + 1)) inputs next = .done (call.values.drop (childIndex + 1)) call.middle ∧
    sizeOf childSyntax < sizeOf (Syntax.node expressions) := checked_witness

end MicroCFTA.OpenOrdinaryLeafSourceCallsFixture
