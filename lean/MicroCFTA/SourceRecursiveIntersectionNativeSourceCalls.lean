import MicroCFTA.SourceRecursiveIntersectionNativeObservations

/-!
# Source meaning of actual native start and hit observations

Actual lookup and demand derive the original captured physical request.
Completed native hits derive concrete guarded kernel replay and current
result availability. Checked word bounds remain explicit. No callback purity
or new completion provenance is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual node start derives captured request identity, strong current facts, and its exact running cell. -/
theorem node_started_source [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (request actual : NodeRequest Symbol Guard)
    (ready : NodeReady state.machine request) (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.evaluate actual, current)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧ actual = request ∧ current.machine = state.machine ∧
      current.nodes.cells handle = some ⟨actual, .evaluating⟩ := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupNode_valid width emptyGuard conjoin state valid request ready safe
  have currentValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current := by
    simpa only [demand] using demandNode_valid width emptyGuard conjoin selected selectedValid handle
  obtain ⟨key, requested, published, machine⟩ := lookupNode_memoized request state selected handle lookup
  have selectedReady : NodeReady selected.machine request := by simpa only [machine] using ready
  have cells := demandNode_evaluate handle selected current actual demand
  have same : actual = request := node_request_exact width emptyGuard conjoin selected selectedValid request selectedReady key
    ⟨requested, safe⟩ handle published ⟨actual, .suspended⟩ cells.1
  have physical : current.machine = selected.machine := by simpa only [demand] using demandNode_machine handle selected
  exact ⟨currentValid, same, physical.trans machine, cells.2⟩

/-- Actual edge start derives captured row identity, strong current facts, and its exact running cell. -/
theorem edge_started_source [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (request actual : EdgeRequest Symbol Guard)
    (ready : EdgeReady state.machine request) (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.evaluate actual, current)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧ actual = request ∧ current.machine = state.machine ∧
      current.edges.cells handle = some ⟨actual, .evaluating⟩ := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupEdge_valid width emptyGuard conjoin state valid request ready safe
  have currentValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current := by
    simpa only [demand] using demandEdge_valid width emptyGuard conjoin selected selectedValid handle
  obtain ⟨published, machine⟩ := lookupEdge_selected request state selected handle lookup
  have selectedReady : EdgeReady selected.machine request := by simpa only [machine] using ready
  have cells := demandEdge_evaluate handle selected current actual demand
  have same : actual = request := edge_request_exact width emptyGuard conjoin selected selectedValid request selectedReady _
    ⟨rfl, safe⟩ handle published ⟨actual, .suspended⟩ cells.1
  have physical : current.machine = selected.machine := by simpa only [demand] using demandEdge_machine handle selected
  exact ⟨currentValid, same, physical.trans machine, cells.2⟩

/-- An actual completed native node hit derives stable guarded kernel replay without physical effects. -/
theorem node_ready_source [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (request : NodeRequest Symbol Guard)
    (ready : NodeReady state.machine request) (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (value : Value Symbol Guard) (lookup : lookupNode width request state = (.memoized handle, selected))
    (demand : demandNode handle selected = (.ready value, current)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧ current.machine = state.machine ∧
      Available current.machine.heap value ∧ ∃ fuel, ∀ extra,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain request.left request.right state.machine = .done value current.machine := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupNode_valid width emptyGuard conjoin state valid request ready safe
  obtain ⟨key, requested, published, machine⟩ := lookupNode_memoized request state selected handle lookup
  obtain ⟨original, stored, retained⟩ := demandNode_ready handle selected current value demand
  subst current
  have selectedReady : NodeReady selected.machine request := by simpa only [machine] using ready
  have replay := node_ready_replay width emptyGuard conjoin selected selectedValid request original selectedReady key
    ⟨requested, safe⟩ handle published value stored
  obtain ⟨fuel, repeated⟩ := replay.2.2.2
  refine ⟨selectedValid, machine, replay.2.2.1, fuel, ?_⟩
  intro extra
  simpa only [machine] using repeated extra

/-- An actual completed native edge hit derives stable guarded row replay without physical effects. -/
theorem edge_ready_source [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state selected current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (request : EdgeRequest Symbol Guard)
    (ready : EdgeReady state.machine request) (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (value : EdgeValue Symbol Guard) (lookup : lookupEdge width request state = (handle, selected))
    (demand : demandEdge handle selected = (.ready value, current)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧ current.machine = state.machine ∧
      EdgeResident current.machine.heap value ∧ ∃ fuel, ∀ extra,
        SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
          (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (fuel + extra) request.domain) request.left request.right state.machine = .done value current.machine := by
  have selectedValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin selected := by
    simpa only [lookup] using lookupEdge_valid width emptyGuard conjoin state valid request ready safe
  obtain ⟨published, machine⟩ := lookupEdge_selected request state selected handle lookup
  obtain ⟨original, stored, retained⟩ := demandEdge_ready handle selected current value demand
  subst current
  have selectedReady : EdgeReady selected.machine request := by simpa only [machine] using ready
  have replay := edge_ready_replay width emptyGuard conjoin selected selectedValid request original selectedReady _
    ⟨rfl, safe⟩ handle published value stored
  obtain ⟨fuel, repeated⟩ := replay.2.2.2
  refine ⟨selectedValid, machine, replay.2.2.1, fuel, ?_⟩
  intro extra
  simpa only [machine] using repeated extra

end MicroCFTA.SourceRecursiveIntersectionNative
