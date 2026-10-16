import MicroCFTA.SourceCurrentAllocatedPartialReads

namespace MicroCFTA.PartialReadsPublicProbe
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialReads
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

#print axioms node_hit
#print axioms edge_hit
#print axioms children_contradiction
#check @NodeCallReads
#check @NodeBodyReads
#check @EdgeCallReads
#check @EdgeBodyReads
#check @RowsReads
#check @DescendantsReads
#check @ChildrenReads
#check @WalkReads

/-- A literal returned logical cell supports a warm request without a supplied lookup answer. -/
def warmNode (checked : Checked width) (merge : Memo) (fourth : Fourth) (request : NodeReq)
    (result : Value Symbol Guard) : Caller width :=
  {SourceCurrentAllocatedPartialState.initial checked merge fourth with
    nodeResults := ⟨put (fun _ => none) request.key 0,
      put (fun _ => none) 0 ⟨request, .returned result⟩, 1⟩}

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
theorem warmNode_started (checked : Checked width) (merge : Memo) (fourth : Fourth) (request : NodeReq)
    (result : Value Symbol Guard) :
    SourceCurrentAllocatedPartialState.beginNode request (warmNode checked merge fourth request result) =
      (0, (.ready result, warmNode checked merge fourth request result)) := by
  simp [warmNode, SourceCurrentAllocatedPartialState.initial, SourceCurrentAllocatedPartialState.beginNode,
    FlatMemoThunk.lookupOrInsert, FlatMemoThunk.demand, put]

-- The same actual warm request has a body-free read schedule with every global table unchanged.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (checked : Checked width) (merge : Memo) (fourth : Fourth) (request : NodeReq)
    (result : Value Symbol Guard) (memos : Memos) :
    NodeCallReads formulas solver (NodeCall.hit (budget := budget) (warmNode_started checked merge fourth request result)) memos memos :=
  .hit (started := warmNode_started checked merge fourth request result)

-- Even if a candidate next bundle is supplied, the actual hit forces literal bundle equality.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (checked : Checked width) (merge : Memo) (fourth : Fourth) (request : NodeReq)
    (result : Value Symbol Guard) (memos saved : Memos)
    (reads : NodeCallReads formulas solver
      (NodeCall.hit (budget := budget) (warmNode_started checked merge fourth request result)) memos saved) : saved = memos :=
  node_hit (warmNode_started checked merge fourth request result) reads

-- A newly selected empty body finishes silently after the actual begin receipt.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (request : NodeReq) (inherited : SourceEqualityConstraintAllocation.Value)
    (before running : Caller width) (handle : Nat) (memos : Memos)
    (started : SourceCurrentAllocatedPartialState.beginNode request before = (handle, (.evaluate ⟨inherited, .empty⟩, running))) :
    NodeCallReads formulas solver (NodeCall.evaluate (budget := budget) started .empty) memos memos :=
  .evaluate (started := started) (body := NodeBody.empty (budget := budget) (inherited := inherited) (before := running)) .empty

-- Contradiction has no head query even when the original child list is nonempty.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (value : Value Symbol Guard) (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos) :
    ChildrenReads formulas solver
      (Children.contradiction (budget := budget) (values := value :: values) (before := before)) memos memos :=
  .contradiction

-- An empty indexed walk makes no global call at any index.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (combined : SourceEqualityConstraintAllocation.Value) (index : Nat) (before : Caller width) (memos : Memos) :
    WalkReads formulas solver (Walk.nil (budget := budget) (combined := combined) (index := index) (before := before)) memos memos :=
  .nil

-- A two-child actual hit walk carries the same complete bundle through both descended requests.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (combined : SourceEqualityConstraintAllocation.Value) (index : Nat)
    (first second firstResult secondResult : Value Symbol Guard) (before middle after : Caller width)
    (firstHandle secondHandle : Nat) (memos : Memos)
    (firstStarted : SourceCurrentAllocatedPartialState.beginNode ⟨(descend before combined index).1, first⟩
      (descend before combined index).2 = (firstHandle, (.ready firstResult, middle)))
    (secondStarted : SourceCurrentAllocatedPartialState.beginNode ⟨(descend middle combined (index + 1)).1, second⟩
      (descend middle combined (index + 1)).2 = (secondHandle, (.ready secondResult, after))) :
    WalkReads formulas solver
      (Walk.cons (NodeCall.hit (budget := budget) firstStarted) (Walk.cons (NodeCall.hit secondStarted) .nil)) memos memos :=
  .cons (first := NodeCall.hit firstStarted) (tail := Walk.cons (NodeCall.hit secondStarted) .nil)
    (.hit (started := firstStarted))
    (.cons (first := NodeCall.hit secondStarted) (tail := Walk.nil)
      (.hit (started := secondStarted)) .nil)

-- Parent reads keep the exact actual checked leaf and its returned bundle.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value} {original result : EdgeValue Symbol Guard}
    {before : Caller width} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {checked : Checked width} {fourth : Fourth} {merge : Memo} {memos saved : Memos}
    (field : SourceEqualityMkEdgeAllocation.contradictory original.entry.key.constraint = false →
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited
      original.children before.checked before.fourth before.merge result checked fourth merge)
    (reads : SourceCurrentAllocatedParentEdge.Reads formulas solver actual memos saved) :
    EdgeBodyReads formulas solver (EdgeBody.parent field actual) memos saved :=
  .parent (field := field) reads

-- A row threads edge-query output into descendant reads, then into the tail; no family is reset.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {original narrowed result : EdgeValue Symbol Guard} {originals results : List (EdgeValue Symbol Guard)}
    {before middle later after : Caller width} {memos edgeMemos childMemos saved : Memos}
    (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
    (children : Descendants budget inherited narrowed middle result later)
    (rest : Rows budget inherited originals later results after)
    (edgeReads : EdgeCallReads formulas solver edge memos edgeMemos)
    (childReads : DescendantsReads formulas solver children edgeMemos childMemos)
    (restReads : RowsReads formulas solver rest childMemos saved) :
    RowsReads formulas solver (Rows.cons edge children rest) memos saved :=
  .cons edgeReads childReads restReads

#print axioms warmNode_started
end MicroCFTA.PartialReadsPublicProbe
