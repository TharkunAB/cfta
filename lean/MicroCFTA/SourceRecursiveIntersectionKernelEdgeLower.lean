import MicroCFTA.SourceRecursiveIntersectionKernelReturnDegree
import MicroCFTA.SourceRecursiveIntersectionKernelLowerSequencing

/-!
# Allocation bounds through actual ordered edge children

Every child outcome retains its reached heap.
Successful children supply the heap invariants for the next call.
Edge construction does not change any complete Mu record.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedNestedFacts InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every actual edge outcome retains the original semantic request's body bound. -/
theorem edge_result_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state : Machine Symbol Guard),
      Valid state → NodeReady state request →
      Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel request.domain request.left request.right state).state.heap)
    (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state : Machine Symbol Guard) (valid : Valid state) (ready : EdgeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap) :
    Lower state.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (edge emptyGuard conjoin (execute emptyGuard conjoin fuel request.domain)
        request.left request.right state).state.heap := by
  let bound := requiredFuel (view source holds) (edgeSemantic holds request) complete
  by_cases sameArity : request.left.children.length = request.right.children.length
  · have childBound (children : Value Symbol Guard × Value Symbol Guard)
        (member : children ∈ request.left.children.zip request.right.children) :
        NodeBelow source holds bound ⟨request.domain, children.1, children.2⟩ := by
      refine ⟨scope.child source facts request children member, ?_⟩
      apply immediate_requiredFuel (view source holds) (edgeSemantic holds request) _ complete
      apply Immediate.edge (SourceRecursiveIntersectionSchedule.domain request.domain.key)
        (row holds request.left) (row holds request.right) (inputOf children.1, inputOf children.2)
      · simpa only [row, List.length_map] using sameArity
      · change (inputOf children.1, inputOf children.2) ∈
          (request.left.children.map inputOf).zip (request.right.children.map inputOf)
        rw [List.zip_map]
        exact List.mem_map.mpr ⟨children, member, rfl⟩
    let requests := request.left.children.zip request.right.children
    let invariant (current : Machine Symbol Guard) : Prop :=
      Valid current ∧ Domain current request.domain ∧
        (∀ children ∈ requests, Available current.heap children.1 ∧ Available current.heap children.2) ∧
        Grows source current.heap ∧ Extends source.nodes.issued current.heap.nodes.issued ∧
        SemanticHeap current.heap ∧ InternedOpenDepthReadback.Heap current.heap
    have limited : ∀ children ∈ requests, ∀ current, invariant current →
        Lower current.heap (limit + bound)
          (execute emptyGuard conjoin fuel request.domain children.1 children.2 current).state.heap := by
      intro children member current currentKnown
      obtain ⟨currentValid, currentDomain, inputs, currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
      obtain ⟨childScope, childComplete, smaller⟩ := childBound children member
      exact (nodeIH ⟨request.domain, children.1, children.2⟩ childScope childComplete current currentValid
        ⟨currentDomain, inputs children member⟩ currentGrowth currentHistory currentSemantic currentOpened).mono
        (Nat.add_le_add_left (Nat.le_of_lt smaller) limit)
    have preserved : ∀ children ∈ requests, ∀ current value after, invariant current →
        execute emptyGuard conjoin fuel request.domain children.1 children.2 current = .done value after → invariant after := by
      intro children member current value after currentKnown done
      obtain ⟨currentValid, currentDomain, inputs, currentGrowth, currentHistory, currentSemantic, currentOpened⟩ := currentKnown
      obtain ⟨childScope, childComplete, _smaller⟩ := childBound children member
      have available := inputs children member
      have checked := execute_checked emptyGuard conjoin fuel request.domain children.1 children.2 current
        currentValid currentDomain available.1 available.2
      have afterValid : Valid after := by simpa only [done, Result.state] using checked.valid
      have extension : Extension current after := by simpa only [done, Result.state] using checked.extension
      obtain ⟨afterSemantic, afterOpened, _degree⟩ := node_result_degree source facts limit sourceBounded
        holds emptyGuard conjoin fuel ⟨request.domain, children.1, children.2⟩ childScope childComplete current after
        currentValid ⟨currentDomain, available⟩ currentGrowth currentHistory currentSemantic currentOpened value done
      exact ⟨afterValid, currentDomain.grows request.domain extension,
        (fun pair included => ⟨extension.available _ (inputs pair included).1,
          extension.available _ (inputs pair included).2⟩),
        grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history, afterSemantic, afterOpened⟩
    have inputs : ∀ children ∈ requests, Available state.heap children.1 ∧ Available state.heap children.2 := by
      intro children member
      have inside := List.of_mem_zip member
      exact ⟨valid.1.cached.edges request.left.entry.key request.left ready.2.1 children.1 inside.1,
        valid.1.cached.edges request.right.entry.key request.right ready.2.2 children.2 inside.2⟩
    have walked := walk_lower (fun children => execute emptyGuard conjoin fuel request.domain children.1 children.2)
      invariant (limit + bound) requests limited preserved state ⟨valid, ready.1, inputs, growth, history, semantic, opened⟩
    simp only [edge, sameArity, ite_true]
    apply result_bind_lower _ _ walked
    intro values after _done accumulated
    exact accumulated
  · simp only [edge, sameArity, ite_false]
    intro key entry body depth ordinary present
    exact Or.inl present

end MicroCFTA.SourceRecursiveIntersectionKernel
