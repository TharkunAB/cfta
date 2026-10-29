import MicroCFTA.SourceRecursiveIntersectionCompileEdgeBounds
import MicroCFTA.SourceRecursiveIntersectionKernelReadback
import MicroCFTA.SourceRecursiveIntersectionKernelEdgeDegree

/-!
# Actual kernel row degree from the smaller runtime-fuel node hypothesis

The node hypothesis applies at one fixed runtime fuel.
Ordered child requests retain their original scope and strict semantic rank.
The actual trace transports both heap invariants between child calls.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedNestedFacts InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- An actual row return derives its degree from the smaller runtime-fuel node hypothesis. -/
theorem edge_result_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (limit fuel : Nat)
    (nodeIH : ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state after : Machine Symbol Guard) (_valid : Valid state) (_ready : NodeReady state request)
      (_growth : Grows source state.heap) (_history : Extends source.nodes.issued state.heap.nodes.issued)
      (_semantic : SemanticHeap state.heap) (_opened : InternedOpenDepthReadback.Heap state.heap)
      (value : Value Symbol Guard),
      execute emptyGuard conjoin fuel request.domain request.left request.right state = .done value after →
      SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
        valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete)
    (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (state after : Machine Symbol Guard) (valid : Valid state) (ready : EdgeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued)
    (semantic : SemanticHeap state.heap) (opened : InternedOpenDepthReadback.Heap state.heap)
    (value : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (execute emptyGuard conjoin fuel request.domain)
      request.left request.right state = .done value after) :
    SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
      manyDepth value.children ≤ limit + requiredFuel (view source holds) (edgeSemantic holds request) complete := by
  let bound := requiredFuel (view source holds) (edgeSemantic holds request) complete
  by_cases sameArity : request.left.children.length = request.right.children.length
  · have childBound (children : Value Symbol Guard × Value Symbol Guard)
        (member : children ∈ request.left.children.zip request.right.children) :
        NodeBelow source holds bound ⟨request.domain, children.1, children.2⟩ := by
      refine ⟨scope.child source sourceFacts request children member, ?_⟩
      apply immediate_requiredFuel (view source holds) (edgeSemantic holds request) _ complete
      apply Immediate.edge (SourceRecursiveIntersectionSchedule.domain request.domain.key)
        (row holds request.left) (row holds request.right) (inputOf children.1, inputOf children.2)
      · simpa only [row, List.length_map] using sameArity
      · change (inputOf children.1, inputOf children.2) ∈
          (request.left.children.map inputOf).zip (request.right.children.map inputOf)
        rw [List.zip_map]
        exact List.mem_map.mpr ⟨children, member, rfl⟩
    have traceBound (requests : List (Value Symbol Guard × Value Symbol Guard))
        (first : Machine Symbol Guard) (values : List (Value Symbol Guard)) (last : Machine Symbol Guard)
        (trace : WalkTrace (fun children => execute emptyGuard conjoin fuel request.domain children.1 children.2)
          requests first values last) :
        (∀ children ∈ requests, NodeBelow source holds bound ⟨request.domain, children.1, children.2⟩) →
        Valid first → Domain first request.domain →
        (∀ children ∈ requests, Available first.heap children.1 ∧ Available first.heap children.2) →
        Grows source first.heap → Extends source.nodes.issued first.heap.nodes.issued →
        SemanticHeap first.heap → InternedOpenDepthReadback.Heap first.heap →
        SemanticHeap last.heap ∧ InternedOpenDepthReadback.Heap last.heap ∧ manyDepth values ≤ limit + bound := by
      induction trace with
      | nil current =>
          intro _ _ _ _ _ _ currentSemantic currentOpened
          exact ⟨currentSemantic, currentOpened, by simpa only [manyDepth] using Nat.zero_le (limit + bound)⟩
      | cons children requests current firstValue middle values last returned _rest ih =>
          intro bounded currentValid known inputs currentGrowth currentHistory currentSemantic currentOpened
          obtain ⟨childScope, childComplete, childLess⟩ := bounded children (by simp)
          have available := inputs children (by simp)
          obtain ⟨middleSemantic, middleOpened, firstDegree⟩ :=
            nodeIH ⟨request.domain, children.1, children.2⟩ childScope childComplete current middle
              currentValid ⟨known, available⟩ currentGrowth currentHistory currentSemantic currentOpened firstValue returned
          have checked := execute_checked emptyGuard conjoin fuel request.domain children.1 children.2 current
            currentValid known available.1 available.2
          have middleValid : Valid middle := by simpa only [returned, Result.state] using checked.valid
          have extension : Extension current middle := by simpa only [returned, Result.state] using checked.extension
          have middleInputs : ∀ pair ∈ requests, Available middle.heap pair.1 ∧ Available middle.heap pair.2 := by
            intro pair member
            have earlier := inputs pair (by simp [member])
            exact ⟨extension.available _ earlier.1, extension.available _ earlier.2⟩
          obtain ⟨lastSemantic, lastOpened, restDegree⟩ := ih
            (fun pair member => bounded pair (by simp [member])) middleValid (known.grows _ extension) middleInputs
            (grows_trans currentGrowth extension.heap) (extends_trans currentHistory extension.history)
            middleSemantic middleOpened
          refine ⟨lastSemantic, lastOpened, ?_⟩
          simpa only [manyDepth] using
            Nat.max_le.mpr ⟨Nat.le_trans firstDegree (Nat.add_le_add_left (Nat.le_of_lt childLess) limit), restDegree⟩
    have inputs : ∀ children ∈ request.left.children.zip request.right.children,
        Available state.heap children.1 ∧ Available state.heap children.2 := by
      intro children member
      have inside := List.of_mem_zip member
      exact ⟨valid.1.cached.edges request.left.entry.key request.left ready.2.1 children.1 inside.1,
        valid.1.cached.edges request.right.entry.key request.right ready.2.2 children.2 inside.2⟩
    have checked := children_checked (execute emptyGuard conjoin fuel) (execute_checked emptyGuard conjoin fuel)
      request.domain (request.left.children.zip request.right.children) state valid ready.1 inputs
    simp only [edge, sameArity, ite_true] at done
    cases walked : walk (fun children => execute emptyGuard conjoin fuel request.domain children.1 children.2)
        (request.left.children.zip request.right.children) state with
    | failed reason middle => simp only [walked, Result.bind] at done; cases done
    | done children middle =>
        have available := checked.result children middle walked
        obtain ⟨middleSemantic, middleOpened, childrenDegree⟩ := traceBound _ state children middle
          ((walk_done_iff _ _ _ _ _).mp walked) childBound valid ready.1 inputs growth history semantic opened
        simp only [walked, Result.bind] at done
        obtain ⟨sameValue, sameAfter⟩ := work_done _ middle value after done
        rw [sameAfter, sameValue]
        refine ⟨SourceRecursiveIntersectionSemanticHeap.edge request.left.entry.key.symbol
          (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) children middle.heap middleSemantic available,
          SourceRecursiveIntersectionOpenDepthEffects.edge request.left.entry.key.symbol
            (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) children middle.heap middleOpened, ?_⟩
        rw [InternedShallowValues.makeEdge_children request.left.entry.key.symbol
          (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) children middle.heap
          middleSemantic.1.normal.facts.coherent middleSemantic.1.normal.facts.cached available]
        exact childrenDegree
  · obtain ⟨afterSemantic, afterOpened, zero⟩ := edge_mismatched_degree emptyGuard conjoin
      (execute emptyGuard conjoin fuel request.domain) request.left request.right state after value sameArity semantic opened done
    exact ⟨afterSemantic, afterOpened, by rw [zero]; exact Nat.zero_le _⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
