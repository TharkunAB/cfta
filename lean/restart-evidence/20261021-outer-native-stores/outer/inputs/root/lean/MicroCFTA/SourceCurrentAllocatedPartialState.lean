import MicroCFTA.SourceCurrentAllocatedNativeEffects
import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.SourceCurrentEmptinessMemo
import MicroCFTA.SourceEqualityConstraintAllocation
import MicroCFTA.FlatMemoThunkRunning
import MicroCFTA.FlatMemoThunkReturned

/-!
# Both result-table families in the current checked caller state

Requests use inherited values already allocated in the current equality
cache. Lookup publishes before demand. Each cell keeps its first request.
Busy and absent observations remain distinct from a returned result.
This protocol describes serial logical demand, not host scheduling.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialState
open Cache InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "MergeMemo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo

/-- Outer requests use the allocated inherited identity and tagged node reference. -/
abbrev NodeKey := Option Nat × InternedBinderProtocol.NodeRef

/-- Reduced-edge requests use a separate family keyed by the complete edge identity. -/
abbrev EdgeKey := Option Nat × Nat

/-- Every published node cell retains both complete original arguments. -/
structure NodeRequest where
  inherited : EqValue
  value : Node

/-- Every published edge cell retains both complete original arguments. -/
structure EdgeRequest where
  inherited : EqValue
  value : Edge

/-- Node preparation reads existing identities and allocates no equality value. -/
def NodeRequest.key (request : NodeRequest) : NodeKey :=
  (request.inherited.identity, request.value.referenceOf)

/-- Edge preparation reads existing identities and allocates no equality value. -/
def EdgeRequest.key (request : EdgeRequest) : EdgeKey :=
  (request.inherited.identity, request.value.entry.identity)

/-- Every continuation carries the complete checked state and all caller result tables. -/
structure State (width : Nat) : Type 1 where
  checked : Checked width
  merge : MergeMemo
  fourth : Fourth
  nodeResults : FlatMemoThunk.State NodeKey NodeRequest Node
  edgeResults : FlatMemoThunk.State EdgeKey EdgeRequest Edge

/-- A fresh caller family clears only its two result tables. -/
def initial (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) : State width :=
  ⟨checked, merge, fourth, FlatMemoThunk.empty, FlatMemoThunk.empty⟩

/-- Current checked operations retain both caller result tables. -/
def advance (before : State width) (checked : Checked width) (fourth : Fourth) (merge : MergeMemo) : State width :=
  { before with checked := checked, merge := merge, fourth := fourth }

/-- Publish and demand the actual outer request in its own table. -/
def beginNode (request : NodeRequest) (before : State width) :
    Nat × (FlatMemoThunk.Observation NodeRequest Node × State width) :=
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  let demanded := FlatMemoThunk.demand published.1 published.2
  (published.1, demanded.1, { before with nodeResults := demanded.2 })

/-- Publish and demand the actual reduced-edge request in its own table. -/
def beginEdge (request : EdgeRequest) (before : State width) :
    Nat × (FlatMemoThunk.Observation EdgeRequest Edge × State width) :=
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  let demanded := FlatMemoThunk.demand published.1 published.2
  (published.1, demanded.1, { before with edgeResults := demanded.2 })

/-- Only an evaluating node cell can receive this completed body result. -/
def finishNode (handle : Nat) (result : Node) (before : State width) : State width :=
  { before with nodeResults := FlatMemoThunk.finish handle result before.nodeResults }

/-- Only an evaluating edge cell can receive this completed body result. -/
def finishEdge (handle : Nat) (result : Edge) (before : State width) : State width :=
  { before with edgeResults := FlatMemoThunk.finish handle result before.edgeResults }

/-- Stored inherited requests retain their exact physical key in the current operation cache. -/
def NodeLinked (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (request : NodeRequest) (key : NodeKey) : Prop :=
  SourceEqualityConstraintAllocation.Stored cache request.inherited ∧ request.key = key

/-- The edge family uses the same current equality cache and its own edge key. -/
def EdgeLinked (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (request : EdgeRequest) (key : EdgeKey) : Prop :=
  SourceEqualityConstraintAllocation.Stored cache request.inherited ∧ request.key = key

/-- Structural validity retains every original request in all three phases. -/
structure Valid (state : State width) : Prop where
  nodes : FlatMemoThunk.Valid (NodeLinked state.checked.operations.constraints) (fun _ => True) state.nodeResults
  edges : FlatMemoThunk.Valid (EdgeLinked state.checked.operations.constraints) (fun _ => True) state.edgeResults

/-- Caller initialization retains all supplied warm state components. -/
theorem initial_components (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) :
    (initial checked merge fourth).checked = checked ∧
    (initial checked merge fourth).merge = merge ∧ (initial checked merge fourth).fourth = fourth ∧
    (initial checked merge fourth).nodeResults = FlatMemoThunk.empty ∧
    (initial checked merge fourth).edgeResults = FlatMemoThunk.empty := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Physical advancement retains both complete caller result tables. -/
theorem advance_tables (before : State width) (checked : Checked width) (fourth : Fourth) (merge : MergeMemo) :
    (advance before checked fourth merge).checked = checked ∧
    (advance before checked fourth merge).fourth = fourth ∧ (advance before checked fourth merge).merge = merge ∧
    (advance before checked fourth merge).nodeResults = before.nodeResults ∧
    (advance before checked fourth merge).edgeResults = before.edgeResults := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Node publication and demand change only their own result table. -/
theorem beginNode_components (request : NodeRequest) (before : State width) :
    let after := (beginNode request before).2.2
    after.checked = before.checked ∧ after.merge = before.merge ∧ after.fourth = before.fourth ∧
      after.edgeResults = before.edgeResults := ⟨rfl, rfl, rfl, rfl⟩

/-- Edge publication and demand change only their own result table. -/
theorem beginEdge_components (request : EdgeRequest) (before : State width) :
    let after := (beginEdge request before).2.2
    after.checked = before.checked ∧ after.merge = before.merge ∧ after.fourth = before.fourth ∧
      after.nodeResults = before.nodeResults := ⟨rfl, rfl, rfl, rfl⟩

/-- Node completion changes only its selected result table. -/
theorem finishNode_components (handle : Nat) (result : Node) (before : State width) :
    (finishNode handle result before).checked = before.checked ∧
    (finishNode handle result before).merge = before.merge ∧ (finishNode handle result before).fourth = before.fourth ∧
    (finishNode handle result before).edgeResults = before.edgeResults := ⟨rfl, rfl, rfl, rfl⟩

/-- Edge completion changes only its selected result table. -/
theorem finishEdge_components (handle : Nat) (result : Edge) (before : State width) :
    (finishEdge handle result before).checked = before.checked ∧
    (finishEdge handle result before).merge = before.merge ∧ (finishEdge handle result before).fourth = before.fourth ∧
    (finishEdge handle result before).nodeResults = before.nodeResults := ⟨rfl, rfl, rfl, rfl⟩

/-- A literal ready node hit returns its first result and identical complete state. -/
theorem beginNode_ready (candidate original : NodeRequest) (before : State width) (handle : Nat) (result : Node)
    (published : before.nodeResults.table candidate.key = some handle)
    (returned : before.nodeResults.cells handle = some ⟨original, .returned result⟩) :
    beginNode candidate before = (handle, .ready result, before) := by
  simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
    FlatMemoThunk.demand_ready _ _ _ _ returned]

/-- A literal ready edge hit returns its first result and identical complete state. -/
theorem beginEdge_ready (candidate original : EdgeRequest) (before : State width) (handle : Nat) (result : Edge)
    (published : before.edgeResults.table candidate.key = some handle)
    (returned : before.edgeResults.cells handle = some ⟨original, .returned result⟩) :
    beginEdge candidate before = (handle, .ready result, before) := by
  simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
    FlatMemoThunk.demand_ready _ _ _ _ returned]

/-- A running node hit remains a busy observation in the same complete state. -/
theorem beginNode_busy (candidate original : NodeRequest) (before : State width) (handle : Nat)
    (published : before.nodeResults.table candidate.key = some handle)
    (running : before.nodeResults.cells handle = some ⟨original, .evaluating⟩) :
    beginNode candidate before = (handle, .busy, before) := by
  simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
    FlatMemoThunk.demand_busy _ _ _ running]

/-- A running edge hit remains a busy observation in the same complete state. -/
theorem beginEdge_busy (candidate original : EdgeRequest) (before : State width) (handle : Nat)
    (published : before.edgeResults.table candidate.key = some handle)
    (running : before.edgeResults.cells handle = some ⟨original, .evaluating⟩) :
    beginEdge candidate before = (handle, .busy, before) := by
  simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
    FlatMemoThunk.demand_busy _ _ _ running]

/-- A suspended node hit starts the original stored request rather than its later candidate. -/
theorem beginNode_suspended (candidate original : NodeRequest) (before : State width) (handle : Nat)
    (published : before.nodeResults.table candidate.key = some handle)
    (suspended : before.nodeResults.cells handle = some ⟨original, .suspended⟩) :
    beginNode candidate before = (handle, .evaluate original,
      { before with nodeResults := FlatMemoThunk.setStatus handle .evaluating before.nodeResults }) := by
  simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published, FlatMemoThunk.demand, suspended]

/-- A suspended edge hit starts the original stored request rather than its later candidate. -/
theorem beginEdge_suspended (candidate original : EdgeRequest) (before : State width) (handle : Nat)
    (published : before.edgeResults.table candidate.key = some handle)
    (suspended : before.edgeResults.cells handle = some ⟨original, .suspended⟩) :
    beginEdge candidate before = (handle, .evaluate original,
      { before with edgeResults := FlatMemoThunk.setStatus handle .evaluating before.edgeResults }) := by
  simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published, FlatMemoThunk.demand, suspended]

/-- Completing a running node retains its exact original request and actual returned value. -/
theorem finishNode_returned (handle : Nat) (original : NodeRequest) (result : Node) (before : State width)
    (running : before.nodeResults.cells handle = some ⟨original, .evaluating⟩) :
    (finishNode handle result before).nodeResults.cells handle = some ⟨original, .returned result⟩ :=
  FlatMemoThunk.finish_evaluating handle result before.nodeResults original running

/-- Completing a running edge retains its exact original request and actual returned value. -/
theorem finishEdge_returned (handle : Nat) (original : EdgeRequest) (result : Edge) (before : State width)
    (running : before.edgeResults.cells handle = some ⟨original, .evaluating⟩) :
    (finishEdge handle result before).edgeResults.cells handle = some ⟨original, .returned result⟩ :=
  FlatMemoThunk.finish_evaluating handle result before.edgeResults original running

/-- No completed node winner can be replaced by a later finish. -/
theorem finishNode_ready (handle : Nat) (original : NodeRequest) (first second : Node) (before : State width)
    (returned : before.nodeResults.cells handle = some ⟨original, .returned first⟩) :
    finishNode handle second before = before := by
  simp only [finishNode, FlatMemoThunk.finish_ready _ _ _ _ _ returned]

/-- No completed edge winner can be replaced by a later finish. -/
theorem finishEdge_ready (handle : Nat) (original : EdgeRequest) (first second : Edge) (before : State width)
    (returned : before.edgeResults.cells handle = some ⟨original, .returned first⟩) :
    finishEdge handle second before = before := by
  simp only [finishEdge, FlatMemoThunk.finish_ready _ _ _ _ _ returned]

/-- Empty caller tables satisfy their key links without supplied cell facts. -/
theorem initial_valid (checked : Checked width) (merge : MergeMemo) (fourth : Fourth) :
    Valid (initial checked merge fourth) :=
  ⟨FlatMemoThunk.empty_valid _ _, FlatMemoThunk.empty_valid _ _⟩

/-- Actual operation-table growth transports both families' original inherited key links. -/
theorem Valid.advance (before : State width) (checked : Checked width) (fourth : Fourth) (merge : MergeMemo)
    (valid : Valid before)
    (growth : Cache.Extends before.checked.operations.constraints.table checked.operations.constraints.table) :
    Valid (advance before checked fourth merge) := by
  constructor
  · exact FlatMemoThunk.Valid.keyMap _ _ _ _ valid.nodes (fun _ _ linked => ⟨linked.1.grows growth, linked.2⟩)
  · exact FlatMemoThunk.Valid.keyMap _ _ _ _ valid.edges (fun _ _ linked => ⟨linked.1.grows growth, linked.2⟩)

/-- Actual node lookup and demand retain both structural result-table invariants. -/
theorem beginNode_valid (request : NodeRequest) (before : State width) (valid : Valid before)
    (stored : SourceEqualityConstraintAllocation.Stored before.checked.operations.constraints request.inherited) :
    Valid (beginNode request before).2.2 := by
  have published := FlatMemoThunk.lookup_valid request.key request before.nodeResults _ _ valid.nodes ⟨stored, rfl⟩ trivial
  exact ⟨FlatMemoThunk.demand_valid _ _ _ published, valid.edges⟩

/-- Actual edge lookup and demand retain both structural result-table invariants. -/
theorem beginEdge_valid (request : EdgeRequest) (before : State width) (valid : Valid before)
    (stored : SourceEqualityConstraintAllocation.Stored before.checked.operations.constraints request.inherited) :
    Valid (beginEdge request before).2.2 := by
  have published := FlatMemoThunk.lookup_valid request.key request before.edgeResults _ _ valid.edges ⟨stored, rfl⟩ trivial
  exact ⟨valid.nodes, FlatMemoThunk.demand_valid _ _ _ published⟩

/-- Node finish retains every stored request's key link. -/
theorem finishNode_valid (handle : Nat) (result : Node) (before : State width) (valid : Valid before) :
    Valid (finishNode handle result before) :=
  ⟨FlatMemoThunk.finish_valid _ _ _ _ valid.nodes, valid.edges⟩

/-- Edge finish retains every stored request's key link. -/
theorem finishEdge_valid (handle : Nat) (result : Edge) (before : State width) (valid : Valid before) :
    Valid (finishEdge handle result before) :=
  ⟨valid.nodes, FlatMemoThunk.finish_valid _ _ _ _ valid.edges⟩

end MicroCFTA.SourceCurrentAllocatedPartialState
