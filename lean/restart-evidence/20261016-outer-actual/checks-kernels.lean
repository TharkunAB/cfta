import MicroCFTA.SourceCurrentAllocatedPartialChecksComposition

namespace MicroCFTA.CurrentChecksCompositionExamples
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

-- An evaluating ordinary node with empty ordered rows needs no machine range supplier.
example (request : NodeReq) (before running : Caller width) (handle : Nat) (inherited : EqValue)
    (entry : Interned InternedBinderProtocol.NodeKey) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (started : beginNode request before = (handle, .evaluate ⟨inherited, .node entry [] depth free⟩, running)) :
    Checks (nodeCallTrace (NodeCall.evaluate (budget := budget) started
      (NodeBody.ordinary (entry := entry) (depth := depth) (free := free) Rows.nil))) := by
  exact SourceCurrentAllocatedPartialChecksComposition.node_evaluate started _ (SourceCurrentAllocatedPartialChecksComposition.ordinary _ SourceCurrentAllocatedPartialChecksComposition.rows_nil)

-- The winning edge's resident range plan yields checks for the exact evaluation, not the candidate's body.
example {request original : EdgeReq} {before running middle : Caller width} {handle : Nat}
    {result : EdgeValue Symbol Guard}
    (started : beginEdge request before = (handle, .evaluate original, running))
    (body : EdgeBody budget original running result middle)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget original running) :
    Checks (edgeCallTrace (EdgeCall.evaluate started body)) ∧
      SourceCurrentAllocatedPartialEdgeActual.CallRanges budget request before := by
  have checked := SourceCurrentAllocatedPartialChecksComposition.edge_evaluate started body (SourceCurrentAllocatedPartialChecksComposition.edge_body body (SourceCurrentAllocatedPartialChecksComposition.resident_ranges ranges))
  exact ⟨checked, checked.edge_call_ranges _⟩

-- Current returned-edge descendants on inherited contradiction skip every child request.
example (value : EdgeValue Symbol Guard) (before : Caller width) :
    let branch := Descendants.run (budget := budget) (edge := value) (inherited := .contradiction)
      (before := before) rfl Children.contradiction
    Checks (descendantsTrace branch) := by
  exact SourceCurrentAllocatedPartialChecksComposition.descendants_run rfl _ SourceCurrentAllocatedPartialChecksComposition.children_contradiction

-- One ordered row composes a warm edge hit, returned-edge contradiction, and its empty suffix.
example (original narrowed : EdgeValue Symbol Guard)
    (before running : Caller width) (handle : Nat)
    (started : beginEdge ⟨.contradiction, original⟩ before = (handle, .ready narrowed, running)) :
    let head := EdgeCall.hit (budget := budget) started
    let descended := Descendants.run (budget := budget) (edge := narrowed) (inherited := .contradiction)
      (before := running) rfl Children.contradiction
    Checks (rowsTrace (Rows.cons head descended Rows.nil)) := by
  exact SourceCurrentAllocatedPartialChecksComposition.rows_cons _ _ _ (SourceCurrentAllocatedPartialChecksComposition.edge_hit started) (SourceCurrentAllocatedPartialChecksComposition.descendants_run rfl _ SourceCurrentAllocatedPartialChecksComposition.children_contradiction) SourceCurrentAllocatedPartialChecksComposition.rows_nil

-- A live child branch composes the literal indexed node hit and tail at the returned state.
example (identity : Nat) (records : List SourceEqualityClassOrder.Record) (value result : Value Symbol Guard)
    (before running : Caller width) (handle : Nat)
    (started : beginNode ⟨(descend before (.live identity records) 0).1, value⟩
      (descend before (.live identity records) 0).2 = (handle, .ready result, running)) :
    Checks (childrenTrace (Children.live (Walk.cons (budget := budget) (NodeCall.hit started) Walk.nil))) := by
  exact SourceCurrentAllocatedPartialChecksComposition.children_live _ (SourceCurrentAllocatedPartialChecksComposition.walk_cons _ _ (SourceCurrentAllocatedPartialChecksComposition.node_hit started) SourceCurrentAllocatedPartialChecksComposition.walk_nil)

-- Literal union and successful Mu leaves require no future edge-body plan.
example (inherited : EqValue) (before : Caller width) (entry : Interned InternedBinderProtocol.NodeKey)
    (members : List (Value Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (body d o result : Value Symbol Guard) (heap : State Symbol Guard)
    (rebuilt : SourceEqualityMuReconstruction.rebuild entry body d o before.checked.native.machine.heap = .done result heap) :
    Checks (nodeBodyTrace (NodeBody.union (budget := budget) (inherited := inherited) (before := before)
      (entry := entry) (members := members) (depth := depth) (free := free))) ∧
    Checks (nodeBodyTrace (NodeBody.binder (budget := budget) (inherited := inherited) rebuilt)) :=
  ⟨SourceCurrentAllocatedPartialChecksComposition.union, SourceCurrentAllocatedPartialChecksComposition.binder rebuilt⟩

end MicroCFTA.CurrentChecksCompositionExamples
