import MicroCFTA.SourceRecursiveIntersectionThunks

/-!
# Retained memo requests through source effects

Demand and completion keep each published request and its original key.
Constructor and domain growth preserve suspended, running, and completed
cells in both native memo families. Completion uses actual source execution
provenance. Recursive callback scheduling is a separate obligation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionThunks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel

/-- Later constructor and domain effects retain original node inputs and completion evidence. -/
theorem nodeGood_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard))
    (good : NodeGood emptyGuard conjoin before cell) : NodeGood emptyGuard conjoin after cell := by
  refine ⟨⟨good.1.1.grows _ growth, growth.available _ good.1.2.1, growth.available _ good.1.2.2⟩, ?_⟩
  cases cell with
  | mk request status =>
    cases status with
    | suspended | evaluating => trivial
    | returned value => exact SourceRecursiveIntersectionMemo.produced_grows emptyGuard conjoin before after growth _ _ _ value good.2

/-- Later source effects retain complete original row records and guarded completion evidence. -/
theorem edgeGood_grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before after : Machine Symbol Guard) (growth : Extension before after)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard))
    (good : EdgeGood emptyGuard conjoin before cell) : EdgeGood emptyGuard conjoin after cell := by
  refine ⟨⟨good.1.1.grows _ growth, edge_grows _ _ growth.heap _ good.1.2.1, edge_grows _ _ growth.heap _ good.1.2.2⟩, ?_⟩
  cases cell with
  | mk request status =>
    cases status with
    | suspended | evaluating => trivial
    | returned value => exact SourceRecursiveIntersectionEdgeMemo.produced_grows emptyGuard conjoin before after growth _ _ _ value good.2

/-- Actual physical and domain effects retain both native memo families. -/
def advance (state : State width Symbol Guard) (after : Machine Symbol Guard) : State width Symbol Guard :=
  { state with machine := after }

/-- Cache growth preserves pending cells as well as complete memo observations. -/
theorem advance_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (after : Machine Symbol Guard) (checked : SourceRecursiveIntersectionKernel.Valid after) (growth : Extension state.machine after) :
    Valid width emptyGuard conjoin (advance state after) :=
  ⟨checked, FlatMemoThunk.Valid.map _ _ _ _ valid.nodes (fun cell good => nodeGood_grows emptyGuard conjoin _ after growth cell good),
    FlatMemoThunk.Valid.map _ _ _ _ valid.edges (fun cell good => edgeGood_grows emptyGuard conjoin _ after growth cell good)⟩

/-- Node demand keeps the edge family and the source machine unchanged. -/
def demandNode (handle : Nat) (state : State width Symbol Guard) :
    FlatMemoThunk.Observation (NodeRequest Symbol Guard) (Value Symbol Guard) × State width Symbol Guard :=
  let (observation, nodes) := FlatMemoThunk.demand handle state.nodes
  (observation, { state with nodes := nodes })

/-- Edge demand keeps the node family and the source machine unchanged. -/
def demandEdge (handle : Nat) (state : State width Symbol Guard) :
    FlatMemoThunk.Observation (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard) × State width Symbol Guard :=
  let (observation, edges) := FlatMemoThunk.demand handle state.edges
  (observation, { state with edges := edges })

/-- Beginning an original node request preserves both native memo invariants. -/
theorem demandNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state) (handle : Nat) :
    Valid width emptyGuard conjoin (demandNode handle state).2 := by
  cases stored : state.nodes.cells handle with
  | none => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid
  | some cell =>
    have good := valid.nodes.checked handle cell stored
    cases cell with
    | mk request status =>
      cases status with
      | suspended =>
        simp only [demandNode, FlatMemoThunk.demand, stored]
        exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle .evaluating state.nodes _ _ valid.nodes _ stored ⟨good.1, trivial⟩, valid.edges⟩
      | evaluating | returned value => simpa only [demandNode, FlatMemoThunk.demand, stored] using valid

/-- Beginning an original edge request preserves both native memo invariants. -/
theorem demandEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state) (handle : Nat) :
    Valid width emptyGuard conjoin (demandEdge handle state).2 := by
  cases stored : state.edges.cells handle with
  | none => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid
  | some cell =>
    have good := valid.edges.checked handle cell stored
    cases cell with
    | mk request status =>
      cases status with
      | suspended =>
        simp only [demandEdge, FlatMemoThunk.demand, stored]
        exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle .evaluating state.edges _ _ valid.edges _ stored ⟨good.1, trivial⟩⟩
      | evaluating | returned value => simpa only [demandEdge, FlatMemoThunk.demand, stored] using valid

/-- Node completion updates only the original running node cell. -/
def finishNode (handle : Nat) (value : Value Symbol Guard) (state : State width Symbol Guard) : State width Symbol Guard :=
  { state with nodes := FlatMemoThunk.finish handle value state.nodes }

/-- Edge completion updates only the original running edge cell. -/
def finishEdge (handle : Nat) (value : EdgeValue Symbol Guard) (state : State width Symbol Guard) : State width Symbol Guard :=
  { state with edges := FlatMemoThunk.finish handle value state.edges }

/-- Actual completed node provenance permits completion of its original published thunk. -/
theorem finishNode_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (produced : SourceRecursiveIntersectionMemo.Produced emptyGuard conjoin state.machine request.domain request.left request.right value) :
    Valid width emptyGuard conjoin (finishNode handle value state) := by
  have good := valid.nodes.checked handle _ running
  simp only [finishNode, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, FlatMemoThunk.setStatus_valid handle (.returned value) state.nodes _ _ valid.nodes _ running ⟨good.1, produced⟩, valid.edges⟩

/-- Actual guarded edge provenance permits completion of its original published thunk. -/
theorem finishEdge_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (produced : SourceRecursiveIntersectionEdgeMemo.Produced emptyGuard conjoin state.machine request.domain request.left request.right value) :
    Valid width emptyGuard conjoin (finishEdge handle value state) := by
  have good := valid.edges.checked handle _ running
  simp only [finishEdge, FlatMemoThunk.finish, running]
  exact ⟨valid.machine, valid.nodes, FlatMemoThunk.setStatus_valid handle (.returned value) state.edges _ _ valid.edges _ running ⟨good.1, produced⟩⟩

/-- An actual completed kernel execution completes its running node cell at the exact returned machine. -/
theorem finishNode_execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩) (fuel : Nat) (value : Value Symbol Guard)
    (final : Machine Symbol Guard)
    (done : execute emptyGuard conjoin fuel request.domain request.left request.right state.machine = .done value final) :
    let after := finishNode handle value (advance state final)
    Valid width emptyGuard conjoin after ∧ after.machine = final ∧ after.edges = state.edges ∧
      after.nodes.table = state.nodes.table ∧ after.nodes.cells handle = some ⟨request, .returned value⟩ := by
  have checked := execute_checked emptyGuard conjoin fuel request.domain request.left request.right state.machine valid.machine ready.1 ready.2.1 ready.2.2
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [done, Result.state] using checked.valid
  have growth : Extension state.machine final := by simpa only [done, Result.state] using checked.extension
  have advanced := advance_valid width emptyGuard conjoin state valid final finalValid growth
  have produced := SourceRecursiveIntersectionMemo.produced_here emptyGuard conjoin fuel request.domain request.left request.right
    state.machine final valid.machine ready.1 ready.2.1 ready.2.2 value done
  refine ⟨finishNode_valid width emptyGuard conjoin _ advanced handle request value running produced, rfl, rfl, ?_, ?_⟩
  · simp only [finishNode, advance, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus]
  · simp [finishNode, advance, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put]

/-- An actual guarded edge execution completes its running edge cell at the exact returned machine. -/
theorem finishEdge_execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩) (fuel : Nat) (value : EdgeValue Symbol Guard)
    (final : Machine Symbol Guard)
    (done : edge emptyGuard conjoin (execute emptyGuard conjoin fuel request.domain) request.left request.right state.machine = .done value final) :
    let after := finishEdge handle value (advance state final)
    Valid width emptyGuard conjoin after ∧ after.machine = final ∧ after.nodes = state.nodes ∧
      after.edges.table = state.edges.table ∧ after.edges.cells handle = some ⟨request, .returned value⟩ := by
  have checked := edge_checked emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) request.domain request.left request.right
    state.machine valid.machine ready.1 ready.2.1 ready.2.2
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [done, Result.state] using checked.valid
  have growth : Extension state.machine final := by simpa only [done, Result.state] using checked.extension
  have advanced := advance_valid width emptyGuard conjoin state valid final finalValid growth
  have produced := SourceRecursiveIntersectionEdgeMemo.produced_here emptyGuard conjoin fuel request.domain request.left request.right
    state.machine final valid.machine ready.1 ready.2.1 ready.2.2 value done
  refine ⟨finishEdge_valid width emptyGuard conjoin _ advanced handle request value running produced, rfl, rfl, ?_, ?_⟩
  · simp only [finishEdge, advance, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus]
  · simp [finishEdge, advance, FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put]

end MicroCFTA.SourceRecursiveIntersectionThunks
