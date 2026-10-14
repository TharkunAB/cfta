import MicroCFTA.SourceRecursiveIntersectionThunkEffects

/-!
# Pending request identity and completed native observations

Checked native keys retain the entire original request while its thunk is
pending. Recursive requests can observe that same running thunk. A completed
native lookup and demand agree with concrete stable guarded kernel replay.
-/
namespace MicroCFTA.SourceRecursiveIntersectionThunks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel

/-- Equality of captured node components gives equality of the complete request. -/
theorem NodeRequest.components (first second : NodeRequest Symbol Guard)
    (same : (first.domain, first.left, first.right) = (second.domain, second.left, second.right)) : first = second := by
  cases first
  cases second
  simp only [Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl⟩
  rfl

/-- Equality of captured row components gives equality of the complete edge request. -/
theorem EdgeRequest.components (first second : EdgeRequest Symbol Guard)
    (same : (first.domain, first.left, first.right) = (second.domain, second.left, second.right)) : first = second := by
  cases first
  cases second
  simp only [Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl⟩
  rfl

/-- A node hit retains its exact original physical request in every thunk phase. -/
theorem node_request_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request : NodeRequest Symbol Guard) (ready : NodeReady state.machine request) (key : Triple width)
    (checked : NodeKey width request key) (handle : Nat) (published : state.nodes.table key = some handle)
    (cell : FlatMemoThunk.Cell (NodeRequest Symbol Guard) (Value Symbol Guard)) (stored : state.nodes.cells handle = some cell) :
    cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := valid.nodes.linked key handle published
  have equal : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := valid.nodes.checked handle cell stored
  exact NodeRequest.components _ _ (SourceRecursiveIntersectionMemo.requestKey_injective width state.machine valid.machine
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1.1 ready.1
    originalKey.2 checked.2 good.1.2.1 good.1.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))

/-- An edge hit retains its exact original domain and complete resident row payloads. -/
theorem edge_request_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request) (key : Triple width)
    (checked : EdgeKeyOf width request key) (handle : Nat) (published : state.edges.table key = some handle)
    (cell : FlatMemoThunk.Cell (EdgeRequest Symbol Guard) (EdgeValue Symbol Guard)) (stored : state.edges.cells handle = some cell) :
    cell.request = request := by
  obtain ⟨original, present, originalKey⟩ := valid.edges.linked key handle published
  have equal : original = cell := Option.some.inj (present.symm.trans stored)
  subst original
  have good := valid.edges.checked handle cell stored
  exact EdgeRequest.components _ _ (SourceRecursiveIntersectionEdgeMemo.requestKey_injective width state.machine valid.machine
    cell.request.domain request.domain cell.request.left cell.request.right request.left request.right good.1.1 ready.1
    originalKey.2 checked.2 good.1.2.1 good.1.2.2 ready.2.1 ready.2.2 (originalKey.1.trans checked.1.symm))

/-- Native node recursion can find the published original thunk before completion. -/
theorem node_recursive_pending (width : Nat) (request candidate : NodeRequest Symbol Guard) (state : State width Symbol Guard)
    (key : Triple width) (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (sameKey : SourceRecursiveIntersectionMemo.requestKey width candidate.domain candidate.left candidate.right = some key)
    (missing : state.nodes.table key = none) :
    let published := (lookupNode width request state).2
    let running := (demandNode state.nodes.next published).2
    (demandNode state.nodes.next published).1 = .evaluate request ∧
    lookupNode width candidate running = (.memoized state.nodes.next, running) ∧
    demandNode state.nodes.next running = (.busy, running) := by
  simp [lookupNode, requested, sameKey, FlatMemoThunk.lookupOrInsert, missing, demandNode,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]

/-- Native edge recursion can find its separate published thunk before completion. -/
theorem edge_recursive_pending (width : Nat) (request candidate : EdgeRequest Symbol Guard) (state : State width Symbol Guard)
    (sameKey : SourceRecursiveIntersectionEdgeMemo.requestKey width candidate.domain candidate.left candidate.right =
      SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right)
    (missing : state.edges.table (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    let published := (lookupEdge width request state).2
    let running := (demandEdge state.edges.next published).2
    (demandEdge state.edges.next published).1 = .evaluate request ∧
    lookupEdge width candidate running = (state.edges.next, running) ∧
    demandEdge state.edges.next running = (.busy, running) := by
  simp [lookupEdge, sameKey, FlatMemoThunk.lookupOrInsert, missing, demandEdge,
    FlatMemoThunk.demand, FlatMemoThunk.setStatus, Cache.put]

/-- A completed native node hit returns exactly the concrete stable source value without effects. -/
theorem node_ready_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request original : NodeRequest Symbol Guard) (ready : NodeReady state.machine request) (key : Triple width)
    (checked : NodeKey width request key) (handle : Nat) (published : state.nodes.table key = some handle)
    (value : Value Symbol Guard) (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    lookupNode width request state = (.memoized handle, state) ∧ demandNode handle state = (.ready value, state) ∧
    Available state.machine.heap value ∧ ∃ fuel, ∀ extra,
      execute emptyGuard conjoin (fuel + extra) request.domain request.left request.right state.machine = .done value state.machine := by
  have same := node_request_exact width emptyGuard conjoin state valid request ready key checked handle published _ stored
  change original = request at same
  subst original
  have good := valid.nodes.checked handle _ stored
  refine ⟨?_, ?_, (SourceRecursiveIntersectionMemo.produced_spec emptyGuard conjoin _ _ _ _ value good.2).2.2.2,
    SourceRecursiveIntersectionMemo.produced_replay emptyGuard conjoin _ _ _ _ value good.2⟩
  · simp only [lookupNode, checked.1, FlatMemoThunk.lookupOrInsert, published]
  · simp only [demandNode, FlatMemoThunk.demand, stored]

/-- A completed native edge hit returns exactly the concrete guarded source row without effects. -/
theorem edge_ready_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (state : State width Symbol Guard) (valid : Valid width emptyGuard conjoin state)
    (request original : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request) (key : Triple width)
    (checked : EdgeKeyOf width request key) (handle : Nat) (published : state.edges.table key = some handle)
    (value : EdgeValue Symbol Guard) (stored : state.edges.cells handle = some ⟨original, .returned value⟩) :
    lookupEdge width request state = (handle, state) ∧ demandEdge handle state = (.ready value, state) ∧
    EdgeResident state.machine.heap value ∧ ∃ fuel, ∀ extra,
      edge emptyGuard conjoin (execute emptyGuard conjoin (fuel + extra) request.domain) request.left request.right state.machine = .done value state.machine := by
  have same := edge_request_exact width emptyGuard conjoin state valid request ready key checked handle published _ stored
  change original = request at same
  subst original
  have good := valid.edges.checked handle _ stored
  refine ⟨?_, ?_, (SourceRecursiveIntersectionEdgeMemo.produced_spec emptyGuard conjoin _ _ _ _ value good.2).2.2.2,
    SourceRecursiveIntersectionEdgeMemo.produced_replay emptyGuard conjoin _ _ _ _ value good.2⟩
  · simp only [lookupEdge, checked.1, FlatMemoThunk.lookupOrInsert, published]
  · simp only [demandEdge, FlatMemoThunk.demand, stored]

end MicroCFTA.SourceRecursiveIntersectionThunks
