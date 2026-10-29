import MicroCFTA.SourceRecursiveIntersectionKernelEdgeLower
import MicroCFTA.SourceRecursiveIntersectionKernelClosedDegree

namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every row-walk outcome retains exact old Mu records or the parent body bound. -/
theorem rows_lower {Symbol Guard : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source) (limit : Nat)
    (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state : Machine Symbol Guard) (_valid : Valid state) (_ready : NodeReady state request)
      (_growth : Grows source state.heap)
      (_history : Extends source.nodes.issued state.heap.nodes.issued)
      (_semantic : SemanticHeap state.heap) (_opened : InternedOpenDepthReadback.Heap state.heap),
      Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel request.domain request.left request.right state).state.heap)
    (bound : Nat) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (rowBounds : ∀ rows ∈ pairs left right, EdgeBelow source holds bound ⟨domain, rows.1, rows.2⟩)
    (state : Machine Symbol Guard) (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.heap row)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap) :
    Lower state.heap (limit + bound)
      (node emptyGuard conjoin (execute emptyGuard conjoin fuel domain) left right state).state.heap := by
  let requests := pairs left right
  let call (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (current : Machine Symbol Guard) :=
    edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain) rows.1 rows.2 current
  let invariant (current : Machine Symbol Guard) : Prop :=
    Valid current ∧ Domain current domain ∧
      (∀ rows ∈ requests, EdgeResident current.heap rows.1 ∧ EdgeResident current.heap rows.2) ∧
      Grows source current.heap ∧ Extends source.nodes.issued current.heap.nodes.issued ∧
      SemanticHeap current.heap ∧ InternedOpenDepthReadback.Heap current.heap
  have limited : ∀ rows ∈ requests, ∀ current, invariant current →
      Lower current.heap (limit + bound) (call rows current).state.heap := by
    intro rows present current currentKnown
    obtain ⟨scope, complete, below⟩ := rowBounds rows present
    obtain ⟨currentValid, currentDomain, currentRows, currentGrowth,
      currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    have resident := currentRows rows present
    exact (edge_result_lower source facts limit sourceBounded holds emptyGuard conjoin fuel nodeIH
      ⟨domain, rows.1, rows.2⟩ scope complete current currentValid ⟨currentDomain, resident⟩
      currentGrowth currentHistory currentSemantic currentOpened).mono
      (Nat.add_le_add_left (Nat.le_of_lt below) limit)
  have preserved : ∀ rows ∈ requests, ∀ current value after, invariant current →
      call rows current = .done value after → invariant after := by
    intro rows present current value after currentKnown completed
    obtain ⟨scope, complete, _below⟩ := rowBounds rows present
    obtain ⟨currentValid, currentDomain, currentRows, currentGrowth,
      currentHistory, currentSemantic, currentOpened⟩ := currentKnown
    have resident := currentRows rows present
    have actual : edge emptyGuard conjoin (execute emptyGuard conjoin fuel domain)
        rows.1 rows.2 current = .done value after := completed
    have checked := edge_checked emptyGuard conjoin (execute emptyGuard conjoin fuel)
      (execute_checked emptyGuard conjoin fuel) domain rows.1 rows.2 current
      currentValid currentDomain resident.1 resident.2
    have afterValid : Valid after := by
      simpa only [actual, Result.state] using checked.valid
    have extension : Extension current after := by
      simpa only [actual, Result.state] using checked.extension
    have retained := row_result_degree source facts limit sourceBounded holds emptyGuard conjoin fuel
      ⟨domain, rows.1, rows.2⟩ scope complete current after currentValid ⟨currentDomain, resident⟩
      currentGrowth currentHistory currentSemantic currentOpened value actual
    exact ⟨afterValid, currentDomain.grows domain extension,
      (fun rows included => ⟨edge_grows _ _ extension.heap _ (currentRows rows included).1,
        edge_grows _ _ extension.heap _ (currentRows rows included).2⟩),
      grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history,
      retained.1, retained.2.1⟩
  have initialRows : ∀ rows ∈ requests, EdgeResident state.heap rows.1 ∧ EdgeResident state.heap rows.2 := by
    intro rows present
    obtain ⟨first, second, _⟩ := (pairs_member left right rows).mp present
    exact ⟨leftResident rows.1 first, rightResident rows.2 second⟩
  have walked := walk_lower call invariant (limit + bound) requests limited preserved state
    ⟨valid, known, initialRows, growth, history, semantic, opened⟩
  have finished := result_bind_lower (walk call requests state)
    (fun rows middle => work (makeNode rows) middle) walked (by
      intro rows middle _completed lower
      change Lower state.heap (limit + bound) (run (makeNode rows) middle.heap).2
      exact preserve middle.heap _ lower (InternedShallowHeap.makeNode_noNewMu rows middle.heap))
  simpa only [node] using finished

end MicroCFTA.SourceRecursiveIntersectionKernel
