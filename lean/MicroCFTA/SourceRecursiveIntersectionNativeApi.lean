import MicroCFTA.SourceRecursiveIntersectionNativeCorrectness

/-!
# Actual completed native node and edge source calls

Actual bounded native completion supplies its evaluation tree. Checked word
bounds on that tree derive complete guarded kernel correspondence and new
memo provenance. No uncached body execution is supplied. Successful first-run
termination for every input remains a separate obligation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- An actual completed native node call derives its exact guarded kernel execution and strong returned memo invariants. -/
theorem native_node_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : NodeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : Value Symbol Guard) (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (done : execute emptyGuard conjoin fuel (.node request .pure) state = .done value after)
    (bounds : Bounds (evaluation_of_done emptyGuard conjoin fuel (.node request .pure) state after value done)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      Available after.machine.heap value ∧ ∃ bound, ∀ extra,
        SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) request.domain request.left request.right state.machine = .done value after.machine := by
  have correct := bounds.correct (fun after value => Available after.heap value) (by intro value; trivial)
    (safe_requestNode request.domain request.left request.right state.machine ready) valid
  obtain ⟨bound, repeated⟩ := correct.meaning
  refine ⟨correct.valid, correct.growth, correct.result, bound, ?_⟩
  intro extra
  have observed := repeated extra
  change (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)
    request.domain request.left request.right state.machine).bind (fun value after => .done value after) = .done value after.machine at observed
  simpa only [result_bind_pure] using observed

/-- An actual completed native edge call derives its exact guarded row execution and strong returned memo invariants. -/
theorem native_edge_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : EdgeValue Symbol Guard) (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (done : execute emptyGuard conjoin fuel (.edge request .pure) state = .done value after)
    (bounds : Bounds (evaluation_of_done emptyGuard conjoin fuel (.edge request .pure) state after value done)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      EdgeResident after.machine.heap value ∧ ∃ bound, ∀ extra,
        SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
          (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) request.domain) request.left request.right state.machine = .done value after.machine := by
  have correct := bounds.correct (fun after value => EdgeResident after.heap value) (by intro value; trivial)
    (safe_requestEdge request.domain request.left request.right state.machine ready) valid
  obtain ⟨bound, repeated⟩ := correct.meaning
  refine ⟨correct.valid, correct.growth, correct.result, bound, ?_⟩
  intro extra
  have observed := repeated extra
  change (SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
    (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra) request.domain)
      request.left request.right state.machine).bind (fun value after => .done value after) = .done value after.machine at observed
  simpa only [result_bind_pure] using observed

/-- Actual native node completion derives concrete source provenance without a supplied kernel execution. -/
theorem native_node_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : NodeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : Value Symbol Guard) (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (done : execute emptyGuard conjoin fuel (.node request .pure) state = .done value after)
    (bounds : Bounds (evaluation_of_done emptyGuard conjoin fuel (.node request .pure) state after value done)) :
    SourceRecursiveIntersectionMemo.Produced emptyGuard conjoin after.machine request.domain request.left request.right value := by
  obtain ⟨_, _, _, bound, repeated⟩ := native_node_correct emptyGuard conjoin fuel request state after value valid ready done bounds
  exact SourceRecursiveIntersectionMemo.produced_here emptyGuard conjoin bound request.domain request.left request.right state.machine after.machine
    valid.machine ready.1 ready.2.1 ready.2.2 value (by simpa only [Nat.add_zero] using repeated 0)

/-- Actual native edge completion derives concrete guarded source provenance without a supplied kernel execution. -/
theorem native_edge_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : EdgeValue Symbol Guard) (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (done : execute emptyGuard conjoin fuel (.edge request .pure) state = .done value after)
    (bounds : Bounds (evaluation_of_done emptyGuard conjoin fuel (.edge request .pure) state after value done)) :
    SourceRecursiveIntersectionEdgeMemo.Produced emptyGuard conjoin after.machine request.domain request.left request.right value := by
  obtain ⟨_, _, _, bound, repeated⟩ := native_edge_correct emptyGuard conjoin fuel request state after value valid ready done bounds
  exact SourceRecursiveIntersectionEdgeMemo.produced_here emptyGuard conjoin bound request.domain request.left request.right state.machine after.machine
    valid.machine ready.1 ready.2.1 ready.2.2 value (by simpa only [Nat.add_zero] using repeated 0)

/-- Empty native memo tables supply initial strong provenance for actual valid physical input caches. -/
theorem cold_node_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (machine : Machine Symbol Guard) (left right : Value Symbol Guard)
    (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) (initial width machine) = .done value after)
    (bounds : Bounds (evaluation_of_done emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width machine) after value done)) :
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧ Extension machine after.machine ∧ Available after.machine.heap value ∧
      SourceRecursiveIntersectionMemo.Produced emptyGuard conjoin after.machine IntersectionEmptyDomain.emptyDomain left right value := by
  have initialValid := initial_valid width emptyGuard conjoin machine valid
  have ready : NodeReady machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := ⟨empty_domain machine, leftAvailable, rightAvailable⟩
  have correct := native_node_correct emptyGuard conjoin fuel _ _ after value initialValid ready done bounds
  exact ⟨correct.1, correct.2.1, correct.2.2.1, native_node_produced emptyGuard conjoin fuel _ _ after value initialValid ready done bounds⟩

end MicroCFTA.SourceRecursiveIntersectionNative
