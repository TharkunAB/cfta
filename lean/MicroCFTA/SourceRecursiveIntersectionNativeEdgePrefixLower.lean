import MicroCFTA.SourceRecursiveIntersectionNativeWalkLower
import MicroCFTA.SourceRecursiveIntersectionNativeReturnDegreeFacts

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode IntersectSchedule
open InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every compiled edge prefix bounds new Mu bodies from its original semantic request. -/
theorem compiled_edge_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source) (limit : Nat)
    (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : EdgeRequest Symbol Guard) (scope : SourceRecursiveIntersectionCode.EdgeScope source request)
    (complete : Completes (view source holds) (edgeSemantic holds request))
    (nodeIH : ∀ (child : NodeRequest Symbol Guard) (_scope : NodeScope source child)
      (childComplete : Completes (view source holds) (nodeSemantic child))
      (_smaller : requiredFuel (view source holds) (nodeSemantic child) childComplete <
        requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → NodeReady current.machine child →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.node child .pure) current →
      ∀ fuel, Lower current.machine.heap
        (limit + requiredFuel (view source holds) (nodeSemantic child) childComplete)
        (execute emptyGuard conjoin fuel (.node child .pure) current).state.machine.heap)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : EdgeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (compileEdge emptyGuard conjoin request) state) (fuel : Nat) :
    Lower state.machine.heap (limit + requiredFuel (view source holds) (edgeSemantic holds request) complete)
      (execute emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) state).state.machine.heap := by
  let bound := requiredFuel (view source holds) (edgeSemantic holds request) complete
  have edgeOld (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
      (heap : InternedConstructorTemplates.State Symbol Guard) :
      InternedShallowHeap.NoNewMu heap (run (makeEdge symbol guard values) heap).2 := by
    intro key entry body depth ordinary present
    exact present
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
    let call (children : Value Symbol Guard × Value Symbol Guard) :=
      requestNode request.domain children.1 children.2
    let invariant (current : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current ∧
      SourceRecursiveIntersectionKernel.Domain current.machine request.domain ∧
      (∀ children ∈ requests, Available current.machine.heap children.1 ∧ Available current.machine.heap children.2) ∧
      Grows source current.machine.heap ∧ Extends source.nodes.issued current.machine.heap.nodes.issued ∧
      SemanticHeap current.machine.heap ∧ InternedOpenDepthReadback.Heap current.machine.heap
    have limited : ∀ children ∈ requests, ∀ current, invariant current →
        WordRanges emptyGuard conjoin (call children) current →
        ∀ childFuel, Lower current.machine.heap (limit + bound)
          (execute emptyGuard conjoin childFuel (call children) current).state.machine.heap := by
      intro children present current currentKnown callRanges childFuel
      obtain ⟨childScope, childComplete, smaller⟩ := childBound children present
      obtain ⟨currentValid, currentDomain, currentInputs, currentGrowth,
        currentHistory, currentSemantic, currentOpened⟩ := currentKnown
      exact (nodeIH ⟨request.domain, children.1, children.2⟩ childScope childComplete smaller current
        currentValid ⟨currentDomain, currentInputs children present⟩ currentGrowth currentHistory
        currentSemantic currentOpened callRanges childFuel).mono
        (Nat.add_le_add_left (Nat.le_of_lt smaller) limit)
    have preserved : ∀ children ∈ requests, ∀ current, invariant current →
        WordRanges emptyGuard conjoin (call children) current →
        ∀ inner value after, execute emptyGuard conjoin inner (call children) current = .done value after →
          invariant after := by
      intro children present current currentKnown callRanges inner value after completed
      obtain ⟨childScope, childComplete, _smaller⟩ := childBound children present
      obtain ⟨currentValid, currentDomain, currentInputs, currentGrowth,
        currentHistory, currentSemantic, currentOpened⟩ := currentKnown
      obtain ⟨afterValid, extension, _available, afterSemantic, afterOpened, _degree⟩ :=
        node_return_degree_facts source facts limit sourceBounded holds width emptyGuard conjoin inner
          ⟨request.domain, children.1, children.2⟩ childScope childComplete current after currentValid
          ⟨currentDomain, currentInputs children present⟩ currentGrowth currentHistory
          currentSemantic currentOpened callRanges value completed
      exact ⟨afterValid, currentDomain.grows request.domain extension,
        (fun children included => ⟨extension.available children.1 (currentInputs children included).1,
          extension.available children.2 (currentInputs children included).2⟩),
        grows_trans currentGrowth extension.heap, extends_trans currentHistory extension.history,
        afterSemantic, afterOpened⟩
    have inputs : ∀ children ∈ requests, Available state.machine.heap children.1 ∧ Available state.machine.heap children.2 := by
      intro children member
      have inside := List.of_mem_zip member
      exact ⟨valid.machine.1.cached.edges request.left.entry.key request.left ready.2.1 children.1 inside.1,
        valid.machine.1.cached.edges request.right.entry.key request.right ready.2.2 children.2 inside.2⟩
    simp only [compileEdge, sameArity, ite_true] at ranges ⊢
    have walkRanges : WordRanges emptyGuard conjoin (walk call requests) state :=
      ranges.before_bind emptyGuard conjoin (walk call requests)
        (fun values => .work (makeEdge request.left.entry.key.symbol
          (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) values) .pure) state
    apply execute_bind_lower emptyGuard conjoin fuel (walk call requests)
      (fun values => .work (makeEdge request.left.entry.key.symbol
        (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) values) .pure) state (limit + bound)
    · intro walkFuel
      exact walk_prefix_lower emptyGuard conjoin call invariant (limit + bound) requests limited preserved state
        ⟨valid, ready.1, inputs, growth, history, semantic, opened⟩ walkRanges walkFuel
    · intro _ values after _ outer
      exact work_lower emptyGuard conjoin outer
        (makeEdge request.left.entry.key.symbol (conjoin request.left.entry.key.constraint request.right.entry.key.constraint) values)
        after (limit + bound) (edgeOld _ _ values after.machine.heap)
  · simp only [compileEdge, sameArity, ite_false]
    exact work_lower emptyGuard conjoin fuel (makeEdge request.left.entry.key.symbol emptyGuard [.empty])
      state (limit + bound) (edgeOld _ _ [.empty] state.machine.heap)

end MicroCFTA.SourceRecursiveIntersectionNative
