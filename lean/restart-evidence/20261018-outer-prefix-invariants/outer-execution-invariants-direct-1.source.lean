import MicroCFTA.SourceCurrentParentOperationInvariants
import MicroCFTA.SourceCurrentOuterExecutionGrowth
import MicroCFTA.SourceCurrentEqualityOperationFixed

/-!
# Physical invariants along actual outer prefixes

Successful earlier calls derive the physical state used by the next call.
Outer cells retain their captured ready inputs and resident returned values.
No cell asserts a language law for its result. The proof does not exclude
an active key collision or bound fresh recursive requests.
-/
namespace MicroCFTA.SourceCurrentOuterPrefixInvariants
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentLowerOperationInvariants (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "NativeGood" => SourceCurrentNativeOperationHeap.Good
variable {width : Nat}

/-- An outer node request has an allocated inherited payload and an available value. -/
def NodeReady (before : Caller width) (request : NodeRequest) : Prop :=
  EqReady before.checked.operations.constraints request.inherited ∧
    Available before.checked.native.machine.heap request.value

/-- An outer edge request has an allocated inherited payload and a resident row. -/
def EdgeReady (before : Caller width) (request : EdgeRequest) : Prop :=
  EqReady before.checked.operations.constraints request.inherited ∧
    EdgeResident before.checked.native.machine.heap request.value

private def NodeCell (before : Caller width) (cell : FlatMemoThunk.Cell NodeRequest Node) : Prop :=
  NodeReady before cell.request ∧ ∀ value, cell.status = .returned value → Available before.checked.native.machine.heap value

private def EdgeCell (before : Caller width) (cell : FlatMemoThunk.Cell EdgeRequest Edge) : Prop :=
  EdgeReady before cell.request ∧ ∀ value, cell.status = .returned value → EdgeResident before.checked.native.machine.heap value

/-- Initial outer cells contain ready captured inputs and only resident completed results. -/
structure Good (before : Caller width) : Prop where
  /-- The checked state retains full physical operation invariants. -/
  checked : NativeGood before.checked
  /-- The merge memo retains available originals and completed results. -/
  stored : Stored before.checked.native.machine.heap before.merge
  /-- Node cells retain their full physical requests and results. -/
  nodes : FlatMemoThunk.Valid (fun request key => request.key = key) (NodeCell before) before.nodeResults
  /-- Edge cells retain their full physical requests and results. -/
  edges : FlatMemoThunk.Valid (fun request key => request.key = key) (EdgeCell before) before.edgeResults

/-- Fresh outer result tables need no preexisting cell premise. -/
theorem initial (before : Checked width) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (fourth : SourceCurrentEmptinessMemo.Memo) (good : NativeGood before)
    (stored : Stored before.native.machine.heap memo) : Good (SourceCurrentAllocatedPartialState.initial before memo fourth) :=
  ⟨good,stored,FlatMemoThunk.empty_valid _ _,FlatMemoThunk.empty_valid _ _⟩

private theorem ready_grows {before after : Caller width} (effect : Effect before.checked after.checked)
    {request : NodeRequest} (ready : NodeReady before request) : NodeReady after request :=
  ⟨ready.1.grows effect.operations.constraint_growth,effect.keeps.available _ ready.2⟩

private theorem edge_ready_grows {before after : Caller width} (effect : Effect before.checked after.checked)
    {request : EdgeRequest} (ready : EdgeReady before request) : EdgeReady after request :=
  ⟨ready.1.grows effect.operations.constraint_growth,edge_grows _ _ effect.keeps.growth _ ready.2⟩

private theorem advance_good {before : Caller width} (good : Good before) (checked : Checked width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (effect : Effect before.checked checked) (stored : Stored checked.native.machine.heap memo) :
    Good (advance before checked fourth memo) := by
  refine ⟨effect.good,stored,?_,?_⟩
  · apply FlatMemoThunk.Valid.map _ _ _ _ good.nodes
    intro cell valid
    exact ⟨ready_grows effect valid.1,fun value returned => effect.keeps.available _ (valid.2 value returned)⟩
  · apply FlatMemoThunk.Valid.map _ _ _ _ good.edges
    intro cell valid
    exact ⟨edge_ready_grows effect valid.1,fun value returned => edge_grows _ _ effect.keeps.growth _ (valid.2 value returned)⟩

private theorem demand_checked (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (ready : Request → Prop) (resident : Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value) state) :
    FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value)
      (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand,found] using valid
      | suspended =>
        simp only [FlatMemoThunk.demand,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found
          ⟨(valid.checked _ _ found).1,by intro value impossible; cases impossible⟩

private theorem begin_node {before : Caller width} (request : NodeRequest) (good : Good before)
    (ready : NodeReady before request) : Good (beginNode request before).2.2 := by
  refine ⟨good.checked,good.stored,?_,good.edges⟩
  apply demand_checked
  exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.nodes rfl
    ⟨ready,by intro value impossible; cases impossible⟩

private theorem begin_edge {before : Caller width} (request : EdgeRequest) (good : Good before)
    (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.nodes,?_⟩
  apply demand_checked
  exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
    ⟨ready,by intro value impossible; cases impossible⟩

private theorem finish_checked (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (ready : Request → Prop) (resident : Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value) state)
    (value : Result) (available : resident value) :
    FlatMemoThunk.Valid keyOf
      (fun cell => ready cell.request ∧ ∀ value, cell.status = .returned value → resident value)
      (FlatMemoThunk.finish handle value state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.finish,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | suspended | returned value => simpa only [FlatMemoThunk.finish,found] using valid
      | evaluating =>
        simp only [FlatMemoThunk.finish,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found
          ⟨(valid.checked _ _ found).1,by intro actual same; cases FlatMemoThunk.Status.returned.inj same; exact available⟩

private theorem finish_node {before : Caller width} (handle : Nat) (value : Node) (good : Good before)
    (available : Available before.checked.native.machine.heap value) : Good (finishNode handle value before) :=
  ⟨good.checked,good.stored,finish_checked _ _ _ _ _ good.nodes value available,good.edges⟩

private theorem finish_edge {before : Caller width} (handle : Nat) (value : Edge) (good : Good before)
    (available : EdgeResident before.checked.native.machine.heap value) : Good (finishEdge handle value before) :=
  ⟨good.checked,good.stored,good.nodes,finish_checked _ _ _ _ _ good.edges value available⟩

private theorem begin_node_owner {before running : Caller width} {request original : NodeRequest}
    {handle : Nat} (good : Good running)
    (started : beginNode request before = (handle,.evaluate original,running)) : NodeReady running original := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.evaluate original,running.nodeResults) at observed
  exact (good.nodes.checked _ _ (FlatMemoThunk.demand_evaluate _ _ _ original observed).2).1

private theorem begin_edge_owner {before running : Caller width} {request original : EdgeRequest}
    {handle : Nat} (good : Good running)
    (started : beginEdge request before = (handle,.evaluate original,running)) : EdgeReady running original := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.evaluate original,running.edgeResults) at observed
  exact (good.edges.checked _ _ (FlatMemoThunk.demand_evaluate _ _ _ original observed).2).1

private theorem begin_node_result {before running : Caller width} {request : NodeRequest} {value : Node}
    {handle : Nat} (good : Good running)
    (started : beginNode request before = (handle,.ready value,running)) : Available running.checked.native.machine.heap value := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready value,running.nodeResults) at observed
  obtain ⟨original,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
  rw [← same] at found
  exact (good.nodes.checked _ _ found).2 value rfl

private theorem begin_edge_result {before running : Caller width} {request : EdgeRequest} {value : Edge}
    {handle : Nat} (good : Good running)
    (started : beginEdge request before = (handle,.ready value,running)) : EdgeResident running.checked.native.machine.heap value := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.edgeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.ready value,running.edgeResults) at observed
  obtain ⟨original,found,same⟩ := FlatMemoThunk.demand_ready_original _ _ value _ observed
  rw [← same] at found
  exact (good.edges.checked _ _ found).2 value rfl

end MicroCFTA.SourceCurrentOuterPrefixInvariants
