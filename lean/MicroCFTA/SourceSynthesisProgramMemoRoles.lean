import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric

/-!
# Conditional Program roles in the actual outer memo tables

Each returned cell relates its captured input to its actual result.
The relation is conditional because Type requests share both tables.
Lookup, demand and physical advance retain existing role certificates.
Publication requires the role implication for its actual evaluating owner.
Ready hits use exact physical request equality in the current valid storage.
These laws do not prove the publication premise for every body, all-reached
role preservation, Type progress, worker completion, or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisProgramMemoRoles
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState (NodeRequest EdgeRequest)
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable {width : Nat} {literal : String → Symbol}

/-- A node body preserves a Program role when its captured input has that role. -/
def NodeRole (literal : String → Symbol) (request : NodeRequest) (result : Node) : Prop :=
  ProgramValue literal request.value → ProgramValue literal result

/-- An edge body preserves a strict Program row when its captured input has that role. -/
def EdgeRole (literal : String → Symbol) (request : EdgeRequest) (result : Edge) : Prop :=
  ProgramEdge literal request.value → ProgramEdge literal result

/-- Both actual outer families retain exact key links and conditional returned roles. -/
structure History (literal : String → Symbol) (before : Caller width) : Prop where
  nodes : FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (NodeRole literal)) before.nodeResults
  edges : FlatMemoThunk.Valid (fun request key => request.key = key)
    (FlatMemoThunk.CellSpec (EdgeRole literal)) before.edgeResults

/-- Empty outer families require no supplied input or result role. -/
theorem initial (literal : String → Symbol) (checked : Checked width) (memo : Memo) (fourth : Fourth) :
    History literal (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Physical caller updates retain both immutable outer result families. -/
theorem advance {before : Caller width} (history : History literal before)
    (checked : Checked width) (fourth : Fourth) (memo : Memo) :
    History literal (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨history.nodes, history.edges⟩

/-- Actual node lookup and demand retain every earlier returned certificate. -/
theorem beginNode {before : Caller width} (history : History literal before) (request : NodeRequest) :
    History literal (SourceCurrentAllocatedPartialState.beginNode request before).2.2 := by
  have inserted := FlatMemoThunk.lookup_valid request.key request before.nodeResults
    (fun request key => request.key = key) (FlatMemoThunk.CellSpec (NodeRole literal)) history.nodes rfl trivial
  exact ⟨FlatMemoThunk.demand_spec _ _ _ _ inserted, history.edges⟩

/-- Actual edge lookup and demand retain every earlier returned certificate. -/
theorem beginEdge {before : Caller width} (history : History literal before) (request : EdgeRequest) :
    History literal (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 := by
  have inserted := FlatMemoThunk.lookup_valid request.key request before.edgeResults
    (fun request key => request.key = key) (FlatMemoThunk.CellSpec (EdgeRole literal)) history.edges rfl trivial
  exact ⟨history.nodes, FlatMemoThunk.demand_spec _ _ _ _ inserted⟩

/-- Node publication uses the proved conditional role of its actual running body. -/
theorem finishNode {before : Caller width} {handle : Nat} {owner : NodeRequest} {value : Node}
    (history : History literal before)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (published : ProgramValue literal owner.value → ProgramValue literal value) :
    History literal (SourceCurrentAllocatedPartialState.finishNode handle value before) := by
  refine ⟨FlatMemoThunk.finish_spec handle value before.nodeResults _ _ history.nodes ?_, history.edges⟩
  intro request found
  have same := congrArg (fun cell : FlatMemoThunk.Cell NodeRequest Node => cell.request)
    (Option.some.inj (running.symm.trans found))
  change owner = request at same
  subst request
  exact published

/-- Edge publication uses the proved conditional role of its actual running body. -/
theorem finishEdge {before : Caller width} {handle : Nat} {owner : EdgeRequest} {value : Edge}
    (history : History literal before)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (published : ProgramEdge literal owner.value → ProgramEdge literal value) :
    History literal (SourceCurrentAllocatedPartialState.finishEdge handle value before) := by
  refine ⟨history.nodes, FlatMemoThunk.finish_spec handle value before.edgeResults _ _ history.edges ?_⟩
  intro request found
  have same := congrArg (fun cell : FlatMemoThunk.Cell EdgeRequest Edge => cell.request)
    (Option.some.inj (running.symm.trans found))
  change owner = request at same
  subst request
  exact published

/-- Equal complete live edge keys identify the entire physical request. -/
theorem edge_same_key {before : Caller width} {first second : EdgeRequest}
    (good : Good before) (left : EdgeReady before first) (right : EdgeReady before second)
    (same : first.key = second.key) : first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ good.checked.operations.constraints
    first.inherited second.inherited left.1 right.1 (congrArg Prod.fst same)
  have values := edge_identity_unique _ good.checked.heap.semantic.1.normal.facts.coherent
    first.value second.value left.2 right.2 (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

private theorem lookup_demand_ready {Key Request Result : Type} [DecidableEq Key]
    (key : Key) (request : Request) (memo : FlatMemoThunk.State Key Request Result) (result : Result)
    (ready : (FlatMemoThunk.demand (FlatMemoThunk.lookupOrInsert key request memo).1
      (FlatMemoThunk.lookupOrInsert key request memo).2).1 = .ready result) :
    ∃ original, memo.table key = some (FlatMemoThunk.lookupOrInsert key request memo).1 ∧
      memo.cells (FlatMemoThunk.lookupOrInsert key request memo).1 = some ⟨original, .returned result⟩ := by
  cases found : memo.table key with
  | none => simp [FlatMemoThunk.lookupOrInsert, found, FlatMemoThunk.demand, Cache.put] at ready
  | some handle =>
      have observed : (FlatMemoThunk.demand handle memo).1 = .ready result := by
        simpa only [FlatMemoThunk.lookupOrInsert, found] using ready
      obtain ⟨original, returned, _same⟩ := FlatMemoThunk.demand_ready_original handle memo result
        (FlatMemoThunk.demand handle memo).2 (Prod.ext observed rfl)
      exact ⟨original, by simp only [FlatMemoThunk.lookupOrInsert, found],
        by simpa only [FlatMemoThunk.lookupOrInsert, found] using returned⟩

/-- A node hit preserves the complete caller and transports a strict role through exact owner equality. -/
theorem node_ready {before after : Caller width} {request : NodeRequest} {handle : Nat} {result : Node}
    (history : History literal before) (good : Good before) (ready : NodeReady before request)
    (started : SourceCurrentAllocatedPartialState.beginNode request before = (handle, .ready result, after))
    (role : ProgramValue literal request.value) : after = before ∧ ProgramValue literal result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready request.key request before.nodeResults result
    (congrArg (fun output => output.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.nodeResults).1 = handle :=
    congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun output => output.2.2)
    (started.symm.trans (SourceCurrentAllocatedPartialState.beginNode_ready
      request owner before handle result published returned))
  obtain ⟨cell, stored, linked⟩ := good.nodes.linked request.key handle published
  have same : cell = ⟨owner, .returned result⟩ := Option.some.inj (stored.symm.trans returned)
  subst cell
  have ownerReady := (good.nodes.checked handle _ returned).1
  have ownerEq := SourceCurrentOuterPrefixInvariants.same_key good ownerReady ready linked
  change owner = request at ownerEq
  have certificate : NodeRole literal owner result := history.nodes.checked handle _ returned
  exact ⟨unchanged, certificate (by simpa only [ownerEq] using role)⟩

/-- An edge hit preserves the complete caller and transports a strict role through exact owner equality. -/
theorem edge_ready {before after : Caller width} {request : EdgeRequest} {handle : Nat} {result : Edge}
    (history : History literal before) (good : Good before) (ready : EdgeReady before request)
    (started : SourceCurrentAllocatedPartialState.beginEdge request before = (handle, .ready result, after))
    (role : ProgramEdge literal request.value) : after = before ∧ ProgramEdge literal result := by
  obtain ⟨owner, published, returned⟩ := lookup_demand_ready request.key request before.edgeResults result
    (congrArg (fun output => output.2.1) started)
  have handles : (FlatMemoThunk.lookupOrInsert request.key request before.edgeResults).1 = handle :=
    congrArg Prod.fst started
  rw [handles] at published returned
  have unchanged := congrArg (fun output => output.2.2)
    (started.symm.trans (SourceCurrentAllocatedPartialState.beginEdge_ready
      request owner before handle result published returned))
  obtain ⟨cell, stored, linked⟩ := good.edges.linked request.key handle published
  have same : cell = ⟨owner, .returned result⟩ := Option.some.inj (stored.symm.trans returned)
  subst cell
  have ownerReady := (good.edges.checked handle _ returned).1
  have ownerEq := edge_same_key good ownerReady ready linked
  change owner = request at ownerEq
  have certificate : EdgeRole literal owner result := history.edges.checked handle _ returned
  exact ⟨unchanged, certificate (by simpa only [ownerEq] using role)⟩

end MicroCFTA.SourceSynthesisProgramMemoRoles
